// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:35 PST by lamport  
//      modified on Tue Feb 22 15:59:47 PST 2000 by yuanyu   

package tlc2.util;

import java.io.*;

public class ObjectPoolStack {

  public ObjectPoolStack(int bufSize, String filePrefix) {
    this.filePrefix = filePrefix;
    this.buf = new Object[bufSize];
    this.hiPool = 0;
    this.isIdle = true;
    this.reader = new Reader();
    this.writer = new Writer();
    this.poolFile = null;
    this.reader.start();
    this.writer.start();
  }

  private String filePrefix;
  private Object[] buf;
  private int hiPool;
  private boolean isIdle;
  private Reader reader;
  private Writer writer;
  private File poolFile;
  
  public final Object[] write(Object[] outBuf)
  throws IOException, InterruptedException {
    synchronized(this) {
      while (!this.isIdle) this.wait();
    }
    Object[] res = this.buf;
    this.buf = outBuf;
    this.poolFile = new File(this.filePrefix + Integer.toString(this.hiPool++));
    this.isIdle = false;
    this.writer.notify();
    return res;
  }

  public final Object[] read(Object[] inBuf)
  throws IOException, InterruptedException {
    if (this.hiPool == 0) return null;
    synchronized(this) {
      while (!this.isIdle) this.wait();
    }
    Object[] res = this.buf;
    this.buf = inBuf;
    this.hiPool--;
    if (this.hiPool > 0) {
      this.poolFile = new File(this.filePrefix + Integer.toString(this.hiPool-1));
      this.isIdle = false;
      this.reader.notify();
    }
    return res;
  }

  public final synchronized void beginChkpt(ObjectOutputStream oos)
  throws IOException {
    oos.writeInt(this.hiPool);
  }

  /* Note that this method is not synchronized. */
  public final void recover(ObjectInputStream ois) throws IOException {
    this.hiPool = ois.readInt();
    if (this.hiPool > 0) {
      this.poolFile = new File(this.filePrefix + Integer.toString(this.hiPool-1));
      this.isIdle = false;
      this.reader.notify();
    }
  }

  class Reader extends Thread {
    public void run() {
      try {
	synchronized(this) {
	  while (true) {
	    while (ObjectPoolStack.this.poolFile == null) {
	      this.wait();
	    }
	    FileInputStream fis = new FileInputStream(ObjectPoolStack.this.poolFile);
	    ObjectInputStream ois = new ObjectInputStream(new BufferedInputStream(fis));
	    for (int i = 0; i < ObjectPoolStack.this.buf.length; i++) {
	      ObjectPoolStack.this.buf[i] = ois.readObject();
	    }
	    ois.close();
	    fis.close();
	    ObjectPoolStack.this.poolFile = null;
	    ObjectPoolStack.this.isIdle = true;
	    ObjectPoolStack.this.notify();	    
	  }
	}
      }
      catch (Exception e) {
	System.err.println("Error: when reading the disk (ObjectPoolStack.Reader.run):\n" +
			   e.getMessage());
	System.exit(1);
      }
    }
  }

  class Writer extends Thread {
    public void run() {
      try {
	synchronized(this) {
	  while (true) {
	    while (ObjectPoolStack.this.poolFile == null) {
	      this.wait();
	    }
	    FileOutputStream fos = new FileOutputStream(ObjectPoolStack.this.poolFile);
	    ObjectOutputStream oos = new ObjectOutputStream(new BufferedOutputStream(fos));
	    for (int i = 0; i < ObjectPoolStack.this.buf.length; i++) {
	      oos.writeObject(ObjectPoolStack.this.buf[i]);
	    }
	    oos.close();
	    fos.close();
	    ObjectPoolStack.this.poolFile = null;
	    ObjectPoolStack.this.isIdle = true;
	    ObjectPoolStack.this.notify();
	  }
	}
      }
      catch (Exception e) {
	System.err.println("Error: when reading the disk (ObjectPoolStack.Writer.run):\n" +
			   e.getMessage());
	System.exit(1);
      }
    }
  }
    
}
