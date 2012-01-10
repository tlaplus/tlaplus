// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:27 PST by lamport  
//      modified on Tue Feb 22 11:56:59 PST 2000 by yuanyu   

package tlc2.util;

import java.io.File;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.TLCState;
import tlc2.value.ValueInputStream;
import util.Assert;

public class StatePoolReader extends Thread {

  public StatePoolReader(int bufSize) {
	  this(bufSize, null);
  }

  public StatePoolReader(int bufSize, File file) {
    this.buf = new TLCState[bufSize];
    this.poolFile = file;
    this.isFull = false;
    this.canRead = false;
  }
  
  private TLCState[] buf;
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
  public final synchronized TLCState[] doWork(TLCState[] deqBuf, File file)
  throws IOException, ClassNotFoundException {
    if (this.isFull) {
      Assert.check(this.poolFile == null, EC.SYSTEM_FILE_NULL);
      TLCState[] res = this.buf;
      this.buf = deqBuf;
      this.poolFile = file;
      this.isFull = false;      // <file, false>
      this.canRead = true;
      this.notify();
      return res;
    }
    else if (this.poolFile != null) {
      ValueInputStream vis = new ValueInputStream(this.poolFile);
      for (int i = 0; i < deqBuf.length; i++) {
	deqBuf[i] = TLCState.Empty.createEmpty();
	deqBuf[i].read(vis);
      }
      vis.close();
      this.poolFile = file;     // <file, false>
      this.canRead = true;
      this.notify();
      return deqBuf;
    }
    else {
      ValueInputStream vis = new ValueInputStream(file);
      for (int i = 0; i < deqBuf.length; i++) {
	deqBuf[i] = TLCState.Empty.createEmpty();
	deqBuf[i].read(vis);
      }
      vis.close();              // <null, false>
      return deqBuf;
    }
  }

  /*
   * Returns the cached buffer if filled. Otherwise, returns null.
   */
  public final synchronized TLCState[] getCache(TLCState[] deqBuf, File file)
  throws IOException, ClassNotFoundException {
    if (this.isFull) {
      Assert.check(this.poolFile == null, EC.SYSTEM_FILE_NULL);
      TLCState[] res = this.buf;
      this.buf = deqBuf;
      this.poolFile = file;
      this.isFull = false;      // <file, false>
      this.canRead = false;
      return res;
    }
    else if (this.poolFile != null && this.canRead) {
      // this should seldom occur.
      ValueInputStream vis = new ValueInputStream(this.poolFile);
      for (int i = 0; i < deqBuf.length; i++) {
	deqBuf[i] = TLCState.Empty.createEmpty();
	deqBuf[i].read(vis);
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
	  this.buf[i] = (TLCState)ois.readObject();
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
	  ValueInputStream vis = new ValueInputStream(this.poolFile);
	  for (int i = 0; i < this.buf.length; i++) {
	    this.buf[i] = TLCState.Empty.createEmpty();
	    this.buf[i].read(vis);
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
