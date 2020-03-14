// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:35 PST by lamport  
//      modified on Tue Feb 22 15:59:47 PST 2000 by yuanyu   

package tlc2.util;

import java.io.File;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

import tlc2.output.EC;
import tlc2.output.MP;
import util.FileUtil;

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
                      ObjectInputStream ois = FileUtil.newOBFIS(ObjectPoolStack.this.poolFile);
                      for (int i = 0; i < ObjectPoolStack.this.buf.length; i++) {
                          ObjectPoolStack.this.buf[i] = ois.readObject();
                      }
                      ois.close();
                      ObjectPoolStack.this.poolFile = null;
                      ObjectPoolStack.this.isIdle = true;
                      ObjectPoolStack.this.notify();	    
                  }
              }
          }
          catch (Exception e) 
          {
              MP.printError(EC.SYSTEM_ERROR_WRITING_POOL, e);
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
                      ObjectOutputStream oos = FileUtil.newOBFOS(ObjectPoolStack.this.poolFile);
                      for (int i = 0; i < ObjectPoolStack.this.buf.length; i++) {
                          oos.writeObject(ObjectPoolStack.this.buf[i]);
                      }
                      oos.close();
                      ObjectPoolStack.this.poolFile = null;
                      ObjectPoolStack.this.isIdle = true;
                      ObjectPoolStack.this.notify();
                  }
              }
          }
          catch (Exception e) 
          {
              MP.printError(EC.SYSTEM_ERROR_READING_POOL, e);
              System.exit(1);
          }
      }
  }
    
}
