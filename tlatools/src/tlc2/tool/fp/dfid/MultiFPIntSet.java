// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:15:53 PST by lamport
//      modified on Tue May 15 11:44:57 PDT 2001 by yuanyu

package tlc2.tool.fp.dfid;

import java.io.IOException;
import java.rmi.RemoteException;

/**
 * An <code>MultiFPInt</code> is a set of 64-bit fingerprints.
 */
public class MultiFPIntSet extends FPIntSet {

  private FPIntSet[] sets;
  private int fpbits;

  public MultiFPIntSet(int bits) throws RemoteException {
    int len = 1 << bits;
    this.sets = new FPIntSet[len];
    for (int i = 0; i < len; i++) {
      this.sets[i] = new MemFPIntSet();
    }
    this.fpbits = 64 - bits;
  }

  public final void init(int numThreads, String metadir, String filename)
  throws IOException {
    for (int i = 0; i < this.sets.length; i++) {
      this.sets[i].init(numThreads, metadir, filename+"_"+i);
    }
  }
  
  /**
   * Returns the number of fingerprints in this set.
   * Warning: The size is only accurate in single-threaded mode.
   */
  public final long size() {
    int sum = 0;
    for (int i = 0; i < this.sets.length; i++) {
      sum += this.sets[i].size();
    }
    return sum;
  }

  public final void setLeveled(long fp) {
    int idx = (int)(fp >>> this.fpbits);
    this.sets[idx].setLeveled(fp);
  }
  
  public final int setStatus(long fp, int status) {
    int idx = (int)(fp >>> this.fpbits);
    return this.sets[idx].setStatus(fp, status);
  }

  /* Returns the status of fp. */
  public final int getStatus(long fp) {
    int idx = (int)(fp >>> this.fpbits);
    return this.sets[idx].getStatus(fp);
  }

  public final boolean allLeveled() {
    for (int i = 0; i < this.sets.length; i++) {
      if (!this.sets[i].allLeveled()) return false;
    }
    return true;
  }

  public final void close() {
    for (int i = 0; i < this.sets.length; i++) {
      this.sets[i].close();
    }
  }

  /* This is not quite correct. */
  public final double checkFPs() throws IOException {
    double res = Double.NEGATIVE_INFINITY;
    for (int i = 0; i < this.sets.length; i++) {
      res = Math.max(res, this.sets[i].checkFPs());
    }
    return res;
  }

  public final void exit(boolean cleanup) throws IOException {
    for (int i = 0; i < this.sets.length; i++) {
      this.sets[i].exit(cleanup);
    }
  }
  
  public final void beginChkpt() throws IOException {
    for (int i = 0; i < this.sets.length; i++) {
      this.sets[i].beginChkpt();
    }
  }
  
  public final void commitChkpt() throws IOException {
    for (int i = 0; i < this.sets.length; i++) {
      this.sets[i].commitChkpt();
    }
  }
       
  public final void recover() throws IOException {
    for (int i = 0; i < this.sets.length; i++) {
      this.sets[i].recover();
    }
  }

  public final void beginChkpt(String filename) throws IOException {
    for (int i = 0; i < this.sets.length; i++) {
      this.sets[i].beginChkpt(filename);
    }
  }
  
  public final void commitChkpt(String filename) throws IOException {
    for (int i = 0; i < this.sets.length; i++) {
      this.sets[i].commitChkpt(filename);
    }
  }
  
  public final void recover(String filename) throws IOException {
    for (int i = 0; i < this.sets.length; i++) {
      this.sets[i].recover(filename);
    }
  }

}
