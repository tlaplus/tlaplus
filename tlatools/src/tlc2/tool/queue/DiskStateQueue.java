// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:25:48 PST by lamport  
//      modified on Thu Feb  8 23:32:12 PST 2001 by yuanyu   

package tlc2.tool.queue;

import java.io.File;
import java.io.IOException;

import tlc2.output.EC;
import tlc2.tool.TLCState;
import tlc2.util.StatePoolReader;
import tlc2.util.StatePoolWriter;
import tlc2.value.ValueInputStream;
import tlc2.value.ValueOutputStream;
import util.Assert;
import util.FileUtil;

/**
 * A {@link DiskStateQueue} uses the local hard disc as a backing store for
 * states. An in-memory buffer of size {@link DiskStateQueue}{@link #BufSize}
 */
public class DiskStateQueue extends StateQueue {
	// TODO dynamic bufsize based on current VM parameters?
	private final static int BufSize = Integer.getInteger(DiskStateQueue.class.getName() + ".BufSize", 8192);;

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
	protected TLCState[] deqBuf, enqBuf;
	protected int deqIndex, enqIndex;
	protected StatePoolReader reader;
	protected StatePoolWriter writer;
	private int loPool, hiPool, lastLoPool, newLastLoPool;
	private File loFile;

	/* Constructors */
	public DiskStateQueue(String diskdir) {
		this.deqBuf = new TLCState[BufSize];
		this.enqBuf = new TLCState[BufSize];
		this.deqIndex = BufSize;
		this.enqIndex = 0;
		this.loPool = 1;
		this.hiPool = 0;
		this.lastLoPool = 0;
		this.filePrefix = diskdir + FileUtil.separator;
		File rFile = new File(this.filePrefix + Integer.toString(0));
		this.reader = new StatePoolReader(BufSize, rFile);
		this.reader.setDaemon(true);
		this.loFile = new File(this.filePrefix + Integer.toString(this.loPool));
		this.reader.start();
		this.writer = new StatePoolWriter(BufSize, this.reader);
		this.writer.setDaemon(true);
		this.writer.start();
	}

	final void enqueueInner(TLCState state) {
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

	final TLCState dequeueInner() {
		if (this.deqIndex == this.deqBuf.length) {
			this.fillDeqBuffer();
		}
		return this.deqBuf[this.deqIndex++];
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
				TLCState[] buf = this.reader.getCache(this.deqBuf, this.loFile);
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
		} catch (Exception e) {
			Assert.fail(EC.SYSTEM_ERROR_READING_STATES, new String[] { "queue",
					(e.getMessage() == null) ? e.toString() : e.getMessage() });
		}
	}

	/* Checkpoint. */
	public final void beginChkpt() throws IOException {
		String filename = this.filePrefix + "queue.tmp";
		ValueOutputStream vos = new ValueOutputStream(filename);
		vos.writeLongNat(this.len);
		vos.writeInt(this.loPool);
		vos.writeInt(this.hiPool);
		vos.writeInt(this.enqIndex);
		vos.writeInt(this.deqIndex);
		for (int i = 0; i < this.enqIndex; i++) {
			this.enqBuf[i].write(vos);
		}
		for (int i = this.deqIndex; i < this.deqBuf.length; i++) {
			this.deqBuf[i].write(vos);
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
		ValueInputStream vis = new ValueInputStream(filename);
		this.len = vis.readInt();
		this.loPool = vis.readInt();
		this.hiPool = vis.readInt();
		this.enqIndex = vis.readInt();
		this.deqIndex = vis.readInt();
		this.lastLoPool = this.loPool - 1;

		for (int i = 0; i < this.enqIndex; i++) {
			this.enqBuf[i] = TLCState.Empty.createEmpty();
			this.enqBuf[i].read(vis);
		}
		for (int i = this.deqIndex; i < this.deqBuf.length; i++) {
			this.deqBuf[i] = TLCState.Empty.createEmpty();
			this.deqBuf[i].read(vis);
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
	}

}
