// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:25:48 PST by lamport  
//      modified on Thu Feb  8 23:32:12 PST 2001 by yuanyu   

package tlc2.tool.queue;

import java.io.EOFException;
import java.io.File;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.nio.file.Files;
import java.util.Arrays;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.value.IValue;
import tlc2.value.IValueInputStream;
import tlc2.value.IValueOutputStream;
import tlc2.value.ValueConstants;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.IntervalValue;
import tlc2.value.impl.ModelValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import util.Assert;
import util.BufferedDataInputStream;
import util.BufferedDataOutputStream;
import util.FileUtil;
import util.IDataInputStream;
import util.IDataOutputStream;
import util.UniqueString;
import util.WrongInvocationException;

/**
 * A {@link DiskByteArrayQueue} uses the local hard disc as a backing store for
 * states. An in-memory buffer of size {@link DiskByteArrayQueue}{@link #BufSize}
 */
public class DiskByteArrayQueue extends ByteArrayQueue {
	// TODO dynamic bufsize based on current VM parameters?
	private final static int BufSize = Integer.getInteger(DiskStateQueue.class.getName() + ".BufSize", 8192);

	/*
	 * Invariants: I1. Entries in deqBuf are in the indices: [deqIndex,
	 * deqBuffer.length ) I2. Entries in enqBuf are in the indices: [ 0,
	 * enqIndex ) I3. 0 <= deqIndex <= deqBuf.length, where deqIndex == 0 =>
	 * buffer full deqIndex == deqBuf.length => buffer empty I4. 0 <= enqIndex
	 * <= enqBuf.length, where enqIndex == 0 => buffer empty enqIndex ==
	 * enqBuf.length => buffer full
	 */

	/* Fields */
	private final String filePrefix;
	protected byte[][] deqBuf, enqBuf;
	protected int deqIndex, enqIndex;
	protected ByteArrayPoolReader reader;
	protected ByteArrayPoolWriter writer;
	
	/**
	 * The SPC takes care of deleting swap files on the lower end of the range
	 * (loPool, hiPool). It terminates, when the first checkpoint is written at
	 * which point checkpointing itself takes care of removing obsolete swap
	 * files.
	 */
	protected final StatePoolCleaner cleaner;
	private int loPool, hiPool, lastLoPool, newLastLoPool;
	private File loFile;
	
	// TESTING ONLY!
	DiskByteArrayQueue() throws IOException {
		this(Files.createTempDirectory("DiskByteArrayQueue").toFile().toString());
	}

	/* Constructors */
	public DiskByteArrayQueue(String diskdir) {
		this.deqBuf = new byte[BufSize][];
		this.enqBuf = new byte[BufSize][];
		this.deqIndex = BufSize;
		this.enqIndex = 0;
		this.loPool = 1;
		this.hiPool = 0;
		this.lastLoPool = 0;
		this.filePrefix = diskdir + FileUtil.separator;
		File rFile = new File(this.filePrefix + Integer.toString(0));
		this.reader = new ByteArrayPoolReader(BufSize, rFile);
		this.reader.setDaemon(true);
		this.loFile = new File(this.filePrefix + Integer.toString(this.loPool));
		this.reader.start();
		this.writer = new ByteArrayPoolWriter(BufSize, this.reader);
		this.writer.setDaemon(true);
		this.writer.start();
		this.cleaner = new StatePoolCleaner();
		this.cleaner.setDaemon(true);
		this.cleaner.start();
	}

	final void enqueueInner(byte[] state) {
		if (this.enqIndex == this.enqBuf.length) {
			// enqBuf is full; flush it to disk
			try {
				String pstr = Integer.toString(this.hiPool);
				File file = new File(this.filePrefix + pstr);
				this.enqBuf = this.writer.doWork(this.enqBuf, file);
				this.hiPool++;
				this.enqIndex = 0;
			} catch (Exception e) {
				Assert.fail(EC.SYSTEM_ERROR_WRITING_STATES,
						new String[] { "queue", (e.getMessage() == null) ? e.toString() : e.getMessage() });
			}
		}
		this.enqBuf[this.enqIndex++] = state;
	}

	final byte[] dequeueInner() {
		if (this.deqIndex == this.deqBuf.length) {
			this.fillDeqBuffer();
		}
		return this.deqBuf[this.deqIndex++];
	}
	
	byte[] peekInner() {
		if (this.deqIndex == this.deqBuf.length) {
			this.fillDeqBuffer();
		}
		return this.deqBuf[this.deqIndex];
	}

	private final void fillDeqBuffer() {
		try {
			if (this.loPool + 1 <= this.hiPool) {
				// We are sure there are disk files.
				if (this.loPool + 1 >= this.hiPool) {
					// potential read-write conflict on a file
					this.writer.ensureWritten();
				}
				this.deqBuf = this.reader.doWork(this.deqBuf, this.loFile);
				this.deqIndex = 0;
				this.loPool++;
				String pstr = Integer.toString(this.loPool);
				this.loFile = new File(this.filePrefix + pstr);
			} else {
				// We still need to check if a file is buffered.
				this.writer.ensureWritten();
				byte[][] buf = this.reader.getCache(this.deqBuf, this.loFile);
				if (buf != null) {
					this.deqBuf = buf;
					this.deqIndex = 0;
					this.loPool++;
					String pstr = Integer.toString(this.loPool);
					this.loFile = new File(this.filePrefix + pstr);
				} else {
					// copy entries from enqBuf to deqBuf.
					this.deqIndex = this.deqBuf.length - this.enqIndex;
					System.arraycopy(this.enqBuf, 0, this.deqBuf, this.deqIndex, this.enqIndex);
					this.enqIndex = 0;
				}
			}
			// Notify the cleaner to do its job unless its waits for more work
			// to pile up.
			if ((loPool - lastLoPool) > 100) { //TODO Take BufSize into account. It defines the disc file size.
				synchronized (this.cleaner) {
					this.cleaner.deleteUpTo = loPool - 1;
					this.cleaner.notifyAll();
				}
			}
		} catch (Exception e) {
			Assert.fail(EC.SYSTEM_ERROR_READING_STATES, new String[] { "queue",
					(e.getMessage() == null) ? e.toString() : e.getMessage() });
		}
	}

	/* Checkpoint. */
	public final void beginChkpt() throws IOException {
		synchronized (this.cleaner) {
			// Checkpointing takes precedence over periodic cleaning
			// (cleaner would otherwise delete checkpoint files as it know
			// nothing of checkpoints).
			this.cleaner.finished = true;
			this.cleaner.notifyAll();
		}
		
		String filename = this.filePrefix + "queue.tmp";
	  	final BufferedDataOutputStream vos = new BufferedDataOutputStream(filename);
		vos.writeLong(this.len);
		vos.writeInt(this.loPool);
		vos.writeInt(this.hiPool);
		vos.writeInt(this.enqIndex);
		vos.writeInt(this.deqIndex);
		for (int i = 0; i < this.enqIndex; i++) {
	  		vos.writeInt(this.enqBuf[i].length);
	  		vos.write(this.enqBuf[i]);
		}
		for (int i = this.deqIndex; i < this.deqBuf.length; i++) {
	  		vos.writeInt(this.deqBuf[i].length);
	  		vos.write(this.deqBuf[i]);
		}
		vos.close();
		this.newLastLoPool = this.loPool - 1;
	}

	public final void commitChkpt() throws IOException {
		for (int i = this.lastLoPool; i < this.newLastLoPool; i++) {
			String pstr = Integer.toString(i);
			File oldPool = new File(this.filePrefix + pstr);
			if (!oldPool.delete()) {
				String msg = "DiskStateQueue.commitChkpt: cannot delete " + oldPool;
				throw new IOException(msg);
			}
		}
		this.lastLoPool = this.newLastLoPool;
		File oldChkpt = new File(this.filePrefix + "queue.chkpt");
		File newChkpt = new File(this.filePrefix + "queue.tmp");
		if ((oldChkpt.exists() && !oldChkpt.delete()) || !newChkpt.renameTo(oldChkpt)) {
			String msg = "DiskStateQueue.commitChkpt: cannot delete " + oldChkpt;
			throw new IOException(msg);
		}
	}

	public final void recover() throws IOException {
		String filename = this.filePrefix + "queue.chkpt";
	  	final BufferedDataInputStream vis = new BufferedDataInputStream(filename);
		this.len = vis.readLong();
		this.loPool = vis.readInt();
		this.hiPool = vis.readInt();
		this.enqIndex = vis.readInt();
		this.deqIndex = vis.readInt();
		this.lastLoPool = this.loPool - 1;

		for (int i = 0; i < this.enqIndex; i++) {
			this.enqBuf[i] = new byte[vis.readInt()];
			vis.read(this.enqBuf[i]);
		}
		for (int i = this.deqIndex; i < this.deqBuf.length; i++) {
			this.deqBuf[i] = new byte[vis.readInt()];
			vis.read(this.deqBuf[i]);
		}
		vis.close();
		File file = new File(this.filePrefix + Integer.toString(this.lastLoPool));
		boolean canRead = (this.lastLoPool < this.hiPool);
		this.reader.restart(file, canRead);
		String pstr = Integer.toString(this.loPool);
		this.loFile = new File(this.filePrefix + pstr);
	}

	public void finishAll() {
		super.finishAll();
		synchronized (this.writer) {
			this.writer.notifyAll();
		}
		synchronized (this.reader) {
			this.reader.setFinished();
			this.reader.notifyAll();
		}
		synchronized (this.cleaner) {
			this.cleaner.finished = true;
			this.cleaner.notifyAll();
		}
	}

	private class StatePoolCleaner extends Thread {

		private volatile boolean finished = false;
		public int deleteUpTo;
		
		private StatePoolCleaner() {
			super("RawTLCStatePoolCleaner");
		}

		/* (non-Javadoc)
		 * @see java.lang.Thread#run()
		 */
		public void run() {
			try {
				synchronized (this) {
					while (!this.finished) {
						this.wait();
						if (this.finished) {
							return;
						}
						
						for (int i = lastLoPool; i < deleteUpTo; i++) {
							final File oldPoolFile = new File(filePrefix + Integer.toString(i));
							if (!oldPoolFile.delete()) {
								// No reason to terminate/kill TLC when the cleanup fails.
								// Contrary to StatePoolReader/Write, cleanup is optional
								// functionality whose purpose is to prevent the disc from
								// filling up. If the cleaner fails, the user can still
								// manually delete the files.
								MP.printWarning(EC.SYSTEM_ERROR_CLEANING_POOL, oldPoolFile.getCanonicalPath());
							}
						}
						lastLoPool = deleteUpTo;
					}
				}
			} catch (Exception e) {
				// Assert.printStack(e);
				MP.printError(EC.SYSTEM_ERROR_CLEANING_POOL, e.getMessage(), e);
				System.exit(1);
			}
		}
	}
	
	private static final class ByteArrayPoolWriter extends Thread {

	    private byte[][] buf;     
	    private File poolFile;           // the file to be written
	    private final ByteArrayPoolReader reader;  // the consumer if not null
	    
	  public ByteArrayPoolWriter(int bufSize, ByteArrayPoolReader reader) {
		  super("RawTLCStatePoolWriter");
	    this.buf = new byte[bufSize][];
	    this.poolFile = null;
	    this.reader = reader;
	  }
	  
	  /*
	   * This method first completes the preceding write if not started.
	   * It then notifies this writer to flush enqBuf to file. In practice,
	   * we expect the preceding write to have been completed. 
	   */
	  public final synchronized byte[][] doWork(byte[][] enqBuf, File file)
	  throws IOException {
	    if (this.poolFile != null) {
	  	  final BufferedDataOutputStream vos = new BufferedDataOutputStream(this.poolFile);
	  	  for (int i = 0; i < this.buf.length; i++) {
	  		  vos.writeInt(this.buf[i].length);
	  		  vos.write(this.buf[i]);
	  	  }
	      vos.close();
	    }
	    byte[][] res = this.buf;
	    this.buf = enqBuf;
	    this.poolFile = file;
	    this.notify();
	    return res;
	  }

	  /* Spin waiting for the write to complete.  */
	  public final void ensureWritten() throws InterruptedException {
	    synchronized(this) {
	      while (this.poolFile != null) {
		this.wait();
	      }
	    }
	  }

	  public final synchronized void beginChkpt(ObjectOutputStream oos)
	  throws IOException {
	    boolean hasFile = (this.poolFile == null) ? false : true;
	    oos.writeBoolean(hasFile);
	    if (hasFile) {
	      oos.writeObject(this.poolFile);
	      for (int i = 0; i < this.buf.length; i++) {
		oos.writeObject(this.buf[i]);
	      }
	    }
	  }

	  /* Note this method is not synchronized.  */
	  public final void recover(ObjectInputStream ois) throws IOException {    
	    boolean hasFile = ois.readBoolean();
	    if (hasFile) {
	      try {
		this.poolFile = (File)ois.readObject();
		for (int i = 0; i < this.buf.length; i++) {
		  this.buf[i] = (byte[])ois.readObject();
		}
	      }
	      catch (ClassNotFoundException e) 
	      {
	          Assert.fail(EC.SYSTEM_CHECKPOINT_RECOVERY_CORRUPT, e);
	      }
	    }
	    else {
	      this.poolFile = null;
	    }
	  }

	  /**
	   * Write "buf" to "poolFile". The objects in the queue are written
	   * using Java's object serialization facilities.
	   */
	  public void run() {
	    try {
	      synchronized(this) {
		while (true) {
		  while (this.poolFile == null) {
		    this.wait();
		    // we are done without ever receiving a pool file
		    if(this.poolFile == null) {
		    	return;
		    }
		  }
		  final BufferedDataOutputStream vos = new BufferedDataOutputStream(this.poolFile);
		  for (int i = 0; i < this.buf.length; i++) {
			  vos.writeInt(this.buf[i].length);
			  vos.write(this.buf[i]);
		  }
		  vos.close();
		  this.poolFile = null;
		  this.notify();
		  if (this.reader != null) this.reader.wakeup();
		}
	      }
	    }
	    catch (Exception e) {
	      // Assert.printStack(e);
	        MP.printError(EC.SYSTEM_ERROR_WRITING_POOL, e.getMessage(), e);
	      System.exit(1);
	    }
	  }
	}
	
	private static final class ByteArrayPoolReader extends Thread {

		  public ByteArrayPoolReader(int bufSize, File file) {
			  super("RawTLCStatePoolReader");
		    this.buf = new byte[bufSize][];
		    this.poolFile = file;
		    this.isFull = false;
		    this.canRead = false;
		  }
		  
		  private byte[][] buf;
		  private File poolFile;      // the file to be read
		  private boolean isFull;     // true iff the buf is filled
		  private boolean canRead;    // true iff the file can be read
		  private boolean finished = false;

		  public final synchronized void wakeup() {
		    this.canRead = true;
		    this.notify();
		  }

		  public final synchronized void restart(File file, boolean canRead) {
		    this.poolFile = file;
		    this.isFull = false;
		    this.canRead = canRead;
		    this.notify();
		  }
		  
		  /*
		   * In the most common case, this method expects to see the buffer is
		   * full, it returns its buffer and notifies this reader to read the
		   * content of the file.
		   */
		  public final synchronized byte[][] doWork(byte[][] deqBuf, File file)
		  throws IOException, ClassNotFoundException {
		    if (this.isFull) {
		      assert this.poolFile == null : EC.SYSTEM_FILE_NULL;
		      byte[][] res = this.buf;
		      this.buf = deqBuf;
		      this.poolFile = file;
		      this.isFull = false;      // <file, false>
		      this.canRead = true;
		      this.notify();
		      return res;
		    }
		    else if (this.poolFile != null) {
		  	  final BufferedDataInputStream vis = new BufferedDataInputStream(this.poolFile);
		  	  for (int i = 0; i < deqBuf.length; i++) {
		      	  deqBuf[i] = new byte[vis.readInt()];
		      	  vis.read(deqBuf[i]);
		  	  }
		      vis.close();
		      this.poolFile = file;     // <file, false>
		      this.canRead = true;
		      this.notify();
		      return deqBuf;
		    }
		    else {
		  	  final BufferedDataInputStream vis = new BufferedDataInputStream(this.poolFile);
		  	  for (int i = 0; i < deqBuf.length; i++) {
		  		  deqBuf[i] = new byte[vis.readInt()];
		      	  vis.read(deqBuf[i]);
		  	  }
		      vis.close();              // <null, false>
		      return deqBuf;
		    }
		  }

		  /*
		   * Returns the cached buffer if filled. Otherwise, returns null.
		   */
		  public final synchronized byte[][] getCache(byte[][] deqBuf, File file)
		  throws IOException, ClassNotFoundException {
		    if (this.isFull) {
		      assert this.poolFile == null : EC.SYSTEM_FILE_NULL;
		      byte[][] res = this.buf;
		      this.buf = deqBuf;
		      this.poolFile = file;
		      this.isFull = false;      // <file, false>
		      this.canRead = false;
		      return res;
		    }
		    else if (this.poolFile != null && this.canRead) {
		      // this should seldom occur.
		  	  final BufferedDataInputStream vis = new BufferedDataInputStream(this.poolFile);
		  	  for (int i = 0; i < deqBuf.length; i++) {
		  		  deqBuf[i] = new byte[vis.readInt()];
		      	  vis.read(deqBuf[i]);
		      }
		      vis.close();
		      // this.poolFile.delete();
		      this.poolFile = file;    // <file, false>
		      this.canRead = false;
		      return deqBuf;
		    }
		    return null;
		  }

		  public final synchronized void beginChkpt(ObjectOutputStream oos)
		  throws IOException {
		    boolean hasFile = this.poolFile != null;
		    oos.writeBoolean(hasFile);
		    oos.writeBoolean(this.canRead);
		    oos.writeBoolean(this.isFull);
		    if (hasFile) {
		      oos.writeObject(this.poolFile);
		    }
		    if (this.isFull) {
		      for (int i = 0; i < this.buf.length; i++) {
			oos.writeObject(this.buf[i]);
		      }
		    }
		  }

		  /* Note that this method is not synchronized. */
		  public final void recover(ObjectInputStream ois) throws IOException {
		    boolean hasFile = ois.readBoolean();
		    this.canRead = ois.readBoolean();
		    this.isFull = ois.readBoolean();
		    try {
		      if (hasFile) {
			this.poolFile = (File)ois.readObject();
		      }
		      if (this.isFull) {
			for (int i = 0; i < this.buf.length; i++) {
			  this.buf[i] = (byte[])ois.readObject();
			}
		      }
		    }
		    catch (ClassNotFoundException e) 
		    {
		      Assert.fail(EC.SYSTEM_CHECKPOINT_RECOVERY_CORRUPT, e);
		    }
		  }
		  
		  /**
		   * Read the contents of "poolFile" into "buf". The objects in the
		   * file are read using Java's object serialization facilities.
		   */
		  public void run() {
		    try {
		      synchronized(this) {
			while (true) {
			  while (this.poolFile == null || this.isFull || !this.canRead) {
			    this.wait();
			    if(this.finished ) {
			    	return;
			    }
			  }
			  final BufferedDataInputStream vis = new BufferedDataInputStream(this.poolFile);
			  for (int i = 0; i < this.buf.length; i++) {
		    	  this.buf[i] = new byte[vis.readInt()];
		    	  vis.read(this.buf[i]);
			  }
			  vis.close();
			  this.poolFile = null;
			  this.isFull = true;       // <null, true>
			}
		      }
		    }
		    catch (Exception e) 
		    {
		      // Assert.printStack(e);
		      MP.printError(EC.SYSTEM_ERROR_READING_POOL, e.getMessage(), e);
		      System.exit(1);
		    }
		  }
		  
		  public void setFinished() {
			  finished = true;
		  }
	}
	
	static final class ByteValueOutputStream implements IValueOutputStream, IDataOutputStream {

		private byte[] bytes;
		
		private int idx;
		
		public ByteValueOutputStream() {
			this.bytes = new byte[16]; // TLCState "header" already has 6 bytes.
			this.idx = 0;
		}
		
	    private void ensureCapacity(int minCap) {
	        if (minCap - bytes.length > 0) {
	            int oldCap = bytes.length;
	            int newCap = oldCap << 1; // double size
	            if (newCap - minCap < 0) {
	            	newCap = minCap;
	            }
	            bytes = Arrays.copyOf(bytes, newCap);
	        }
	    }

		/* (non-Javadoc)
		 * @see tlc2.value.IValueOutputStream#writeShort(short)
		 */
		@Override
		public final void writeShort(short s) throws IOException {
			ensureCapacity(idx + 2);
	        this.bytes[idx++] = (byte) ((s >>> 8) & 0xff);
	        this.bytes[idx++] = (byte) (s & 0xff);
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueOutputStream#writeInt(int)
		 */
		@Override
		public final void writeInt(int i) throws IOException {
			ensureCapacity(idx + 4);
	        this.bytes[idx++] = (byte) ((i >>> 24) & 0xff);
	        this.bytes[idx++] = (byte) ((i >>> 16) & 0xff);
	        this.bytes[idx++] = (byte) ((i >>> 8) & 0xff);
	        this.bytes[idx++] = (byte) (i & 0xff);
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueOutputStream#writeLong(long)
		 */
		@Override
		public final void writeLong(long l) throws IOException {
			ensureCapacity(idx + 8);
	        this.bytes[idx++] = (byte) ((l >>> 56) & 0xff);
	        this.bytes[idx++] = (byte) ((l >>> 48) & 0xff);
	        this.bytes[idx++] = (byte) ((l >>> 40) & 0xff);
	        this.bytes[idx++] = (byte) ((l >>> 32) & 0xff);
	        this.bytes[idx++] = (byte) ((l >>> 24) & 0xff);
	        this.bytes[idx++] = (byte) ((l >>> 16) & 0xff);
	        this.bytes[idx++] = (byte) ((l >>> 8) & 0xff);
	        this.bytes[idx++] = (byte) (l & 0xff);
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueOutputStream#close()
		 */
		@Override
		public final void close() throws IOException {
			// No-op
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueOutputStream#writeShortNat(short)
		 */
		@Override
		public final void writeShortNat(short x) throws IOException {
			if (x > 0x7f) {
				this.writeShort((short) -x);
			} else {
				this.writeByte((byte) x);
			}
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueOutputStream#writeNat(int)
		 */
		@Override
		public final void writeNat(int x) throws IOException {
			if (x > 0x7fff) {
				this.writeInt(-x);
			} else {
				this.writeShort((short) x);
			}
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueOutputStream#writeLongNat(long)
		 */
		@Override
		public final void writeLongNat(long x) throws IOException {
			if (x <= 0x7fffffff) {
				this.writeInt((int) x);
			} else {
				this.writeLong(-x);
			}
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueOutputStream#writeByte(byte)
		 */
		@Override
		public final void writeByte(byte b) throws IOException {
			ensureCapacity(idx + 1);
			this.bytes[idx++] = b;
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueOutputStream#writeBoolean(boolean)
		 */
		@Override
		public final void writeBoolean(boolean bool) throws IOException {
	        byte b = (bool ? (byte)1 : (byte)0);
	        this.writeByte(b);
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueOutputStream#getOutputStream()
		 */
		@Override
		public final IDataOutputStream getOutputStream() {
			return this;
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueOutputStream#put(java.lang.Object)
		 */
		@Override
		public final int put(Object obj) {
			return -1;
		}

		public final byte[] toByteArray() {
			final byte[] copyOf = Arrays.copyOf(bytes, idx);
			idx = 0;
			return copyOf;
		}

		/* (non-Javadoc)
		 * @see util.IDataOutputStream#writeString(java.lang.String)
		 */
		@Override
		public final void writeString(String str) throws IOException {
			final int length = str.length();
			ensureCapacity(idx + length);
			
			final char[] c = new char[length];
			str.getChars(0, length, c, 0);
			
			for (int i = 0; i < c.length; i++) {
				this.bytes[idx++] = (byte) c[i];
			}
		}
	}
	
	static final class ByteValueInputStream implements ValueConstants, IValueInputStream, IDataInputStream {

		private final byte[] bytes;
		
		private int idx = 0;

		public ByteValueInputStream(byte[] bytes) {
			this.bytes = bytes;
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueInputStream#read()
		 */
		@Override
		public final IValue read() throws IOException {
			final byte kind = this.readByte();

			switch (kind) {
			case BOOLVALUE: {
				return (this.readBoolean()) ? BoolValue.ValTrue : BoolValue.ValFalse;
			}
			case INTVALUE: {
				return IntValue.gen(this.readInt());
			}
			case STRINGVALUE: {
				return StringValue.createFrom(this);
			}
			case MODELVALUE: {
				return ModelValue.mvs[this.readShort()];
			}
			case INTERVALVALUE: {
				return new IntervalValue(this.readInt(), this.readInt());
			}
			case RECORDVALUE: {
				return RecordValue.createFrom(this);
			}
			case FCNRCDVALUE: {
				return FcnRcdValue.createFrom(this);
			}
			case SETENUMVALUE: {
				return SetEnumValue.createFrom(this);
			}
			case TUPLEVALUE: {
				return TupleValue.createFrom(this);
			}
			default: {
				throw new WrongInvocationException("ValueInputStream: Can not unpickle a value of kind " + kind);
			}
			}
		}

		private final boolean readBoolean() throws EOFException, IOException {
	        return (bytes[idx++] != 0);
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueInputStream#readShort()
		 */
		@Override
		public final int readShort() throws IOException {
	        return (short) ((bytes[idx++] << 8) | (bytes[idx++] & 0xff));
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueInputStream#readInt()
		 */
		@Override
		public final int readInt() throws IOException {
	        int res = bytes[idx++];
	        res <<= 8; res |= (bytes[idx++] & 0xff);
	        res <<= 8; res |= (bytes[idx++] & 0xff);
	        res <<= 8; res |= (bytes[idx++] & 0xff);
	        return res;
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueInputStream#readLong()
		 */
		@Override
		public final long readLong() throws IOException {
	        long res = bytes[idx++];
	        res <<= 8; res |= (bytes[idx++] & 0xff);
	        res <<= 8; res |= (bytes[idx++] & 0xff);
	        res <<= 8; res |= (bytes[idx++] & 0xff);
	        res <<= 8; res |= (bytes[idx++] & 0xff);
	        res <<= 8; res |= (bytes[idx++] & 0xff);
	        res <<= 8; res |= (bytes[idx++] & 0xff);
	        res <<= 8; res |= (bytes[idx++] & 0xff);
	        return res;
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueInputStream#close()
		 */
		@Override
		public final void close() throws IOException {
			// No-op
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueInputStream#readNat()
		 */
		@Override
		public final int readNat() throws IOException {
		    int res = this.readShort();
		    if (res >= 0) return res;
		    res = (res << 16) | (this.readShort() & 0xFFFF);
		    return -res;
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueInputStream#readShortNat()
		 */
		@Override
		public final short readShortNat() throws IOException {
			short res = this.readByte();
			if (res >= 0) return res;
			return (short) -((res << 8) | (this.readByte() & 0xFF));
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueInputStream#readLongNat()
		 */
		@Override
		public final long readLongNat() throws IOException {
		    long res = this.readInt();
		    if (res >= 0) return res;
		    res = (res << 32) | ((long)this.readInt() & 0xFFFFFFFFL);
		    return -res;
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueInputStream#readByte()
		 */
		@Override
		public final byte readByte() throws EOFException, IOException {
			return bytes[idx++];
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueInputStream#assign(java.lang.Object, int)
		 */
		@Override
		public final void assign(Object obj, int idx) {
			// No-op
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueInputStream#getIndex()
		 */
		@Override
		public final int getIndex() {
			return -1;
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueInputStream#getInputStream()
		 */
		@Override
		public final IDataInputStream getInputStream() {
			return this;
		}

		/* (non-Javadoc)
		 * @see tlc2.value.IValueInputStream#getValue(int)
		 */
		@Override
		public final UniqueString getValue(int idx) {
			throw new WrongInvocationException("Not supported");
		}

		/* (non-Javadoc)
		 * @see util.IDataInputStream#readString(int)
		 */
		@Override
		public final String readString(int length) throws IOException {
			final char[] s = new char[length];
			for (int i = 0; i < s.length; i++) {
				s[i] = (char) this.bytes[idx++];
			}
			return new String(s);
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#delete()
	 */
	@Override
	public void delete() {
		finishAll();
		new File(this.filePrefix).delete();
	}
}
