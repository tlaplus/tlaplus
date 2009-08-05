// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:27 PST by lamport
//      modified on Thu Jan 10 18:33:42 PST 2002 by yuanyu

package tlc2.util;

import java.io.File;

import tlc2.output.EC;
import util.Assert;
import util.BufferedDataInputStream;
import util.BufferedDataOutputStream;
import util.FileUtil;

/**
 * Alternative implementation
 * currently not used 
 * 
 * @version $Id$
 */
public final class DiskIntStack {
  private final static int BufSize = 16384;

  private long size;
  private String filePrefix;
  private File poolFile;
  private int[] buf1, buf2, buf, rwbuf;
  private int index;
  private int hiPool;
  private boolean isIdle;
  private Reader reader;
  private Writer writer;
  
  public DiskIntStack(String diskdir, String name) {
    this.size = 0;
    this.buf1 = new int[BufSize];
    this.buf2 = new int[BufSize];
    this.rwbuf = new int[BufSize];
    this.buf = this.buf1;
    this.index = 0;
    this.hiPool = 0;
    this.isIdle = true;
    this.filePrefix = diskdir + FileUtil.separator + name;
    this.poolFile = null;
    this.reader = new Reader();
    this.writer = new Writer();
    this.reader.start();
    this.writer.start();
  }

  /* Return the number of items on the stack. */
  public final long size() { return this.size; }
  
  /* Push an integer onto the stack.  */
  public final synchronized void pushInt(int x) {
    if (this.index == BufSize && this.buf == this.buf2) {
      // need to flush buf1 to disk
      try {
	while (!this.isIdle) this.wait();
	this.buf = this.rwbuf;
	this.rwbuf = this.buf1;
	this.poolFile = new File(this.filePrefix + Integer.toString(this.hiPool++));
	this.isIdle = false;
	this.writer.notify();
	this.buf1 = this.buf2;
	this.buf2 = this.buf;
	this.index = 0;
      }
      catch (Exception e) {
          Assert.fail(EC.SYSTEM_ERROR_WRITING_STATES, new String[]{"stack", e.getMessage()});          
      }
    }
    this.buf[this.index++] = x;
    this.size++;
  }
  
  /* Push a long integer onto the stack.  */
  public final synchronized void pushLong(long x) {
    this.pushInt((int)(x & 0xFFFFFFFFL));
    this.pushInt((int)(x >>> 32));
  }

  /* Pop the integer on top of the stack.  */
  public final synchronized int popInt() {
    if (this.buf == this.buf1 && this.index < BufSize/2 && this.hiPool != 0) {
      // need to fill buf1 from disk
      try {
	while (!this.isIdle) this.wait();
	this.buf = this.rwbuf;
	this.rwbuf = this.buf2;
	this.hiPool--;
	if (this.hiPool > 0) {
	  this.poolFile = new File(this.filePrefix + Integer.toString(this.hiPool-1));
	  this.isIdle = false;
	  this.reader.notify();
	}
	this.buf2 = this.buf1;
	this.buf1 = this.buf;
	this.buf = this.buf2;
      }
      catch (Exception e) {
          Assert.fail(EC.SYSTEM_ERROR_READING_STATES, new String[]{"stack", e.getMessage()});
      }
    }
    this.size--;
    return this.buf[--this.index];
  }

  /* Pop the long integer on top of the stack.  */
  public final synchronized long popLong() {
    long high = this.popInt();
    long low = this.popInt();
    return (high << 32) | (low & 0xFFFFFFFFL);
  }

  class Reader extends Thread {
    public void run() {
      try {
	synchronized(this) {
	  while (true) {
	    while (DiskIntStack.this.poolFile == null) {
	      this.wait();
	    }
	    BufferedDataInputStream bdis = FileUtil.newBdFIS(false, DiskIntStack.this.poolFile);
	    int len = DiskIntStack.this.rwbuf.length;
	    for (int i = 0; i < len; i++) {
	      DiskIntStack.this.rwbuf[i] = bdis.readInt();
	    }
	    bdis.close();
	    DiskIntStack.this.poolFile = null;
	    DiskIntStack.this.isIdle = true;
	    DiskIntStack.this.notify();	    
	  }
	}
      }
      catch (Exception e) 
      {
          Assert.fail(EC.SYSTEM_DISK_IO_ERROR_FOR_FILE, e);
      }
    }
  }

  class Writer extends Thread {
    public void run() {
      try {
	synchronized(this) {
	  while (true) {
	    while (DiskIntStack.this.poolFile == null) {
	      this.wait();
	    }
	    BufferedDataOutputStream bdos = FileUtil.newBdFOS(false, DiskIntStack.this.poolFile);
	    int len = DiskIntStack.this.buf.length;
	    for (int i = 0; i < len; i++) {
	      bdos.writeInt(DiskIntStack.this.buf[i]);
	    }
	    bdos.close();
	    DiskIntStack.this.poolFile = null;
	    DiskIntStack.this.isIdle = true;
	    DiskIntStack.this.notify();
	  }
	}
      }
      catch (Exception e) 
      {
          Assert.fail(EC.SYSTEM_DISK_IO_ERROR_FOR_FILE, e);
      }
    }
  }

}
