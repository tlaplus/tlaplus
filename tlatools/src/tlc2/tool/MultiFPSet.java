// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:16:00 PST by lamport
//      modified on Tue May 15 11:44:57 PDT 2001 by yuanyu

package tlc2.tool;

import java.io.IOException;
import java.io.File;
import java.net.*;
import java.rmi.*;
import java.rmi.server.*;
import java.rmi.registry.*;
import util.Assert;
import tlc2.TLCGlobals;
import tlc2.util.*;

/**
 * An <code>MultiFPSet</code> is a set of 64-bit fingerprints.
 */
public class MultiFPSet extends FPSet {

  private FPSet[] sets;
  private int fpbits;

  /* Create a MultiFPSet with 2^bits FPSets. */
  public MultiFPSet(int bits) throws RemoteException {
    int len = 1 << bits;
    this.sets = new FPSet[len];
    for (int i = 0; i < len; i++) {
      // this.sets[i] = new MemFPSet();
      this.sets[i] = new DiskFPSet(-1);
    }
    this.fpbits = 64 - bits;
  }

  public final void init(int numThreads, String metadir, String filename)
  throws IOException {
    for (int i = 0; i < this.sets.length; i++) {
      this.sets[i].init(numThreads, metadir, filename+"_"+i);
    }
  }
  
  /* Returns the number of fingerprints in this set. */
  public final long size() {
    int sum = 0;
    for (int i = 0; i < this.sets.length; i++) {
      sum += this.sets[i].size();
    }
    return sum;
  }

  /**
   * Returns <code>true</code> iff the fingerprint <code>fp</code> is
   * in this set. If the fingerprint is not in the set, it is added to
   * the set as a side-effect.
   */
  public final boolean put(long fp) throws IOException {
    int idx = (int)(fp >>> this.fpbits);
    return this.sets[idx].put(fp);
  }

  /**
   * Returns <code>true</code> iff the fingerprint <code>fp</code> is
   * in this set.
   */
  public final boolean contains(long fp) throws IOException {
    int idx = (int)(fp >>> this.fpbits);
    return this.sets[idx].contains(fp);
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
      this.sets[i].prepareRecovery();
    }

    long recoverPtr = TLCTrace.getRecoverPtr();
    BufferedRandomAccessFile braf = new BufferedRandomAccessFile(TLCTrace.getFilename(), "r");
    while (braf.getFilePointer() < recoverPtr) {
      braf.readLongNat();      /*drop*/
      long fp = braf.readLong();
      int setIdx = (int)(fp >>> this.fpbits);
      this.sets[setIdx].recoverFP(fp);
    }

    for (int i = 0; i < this.sets.length; i++) {
      this.sets[i].completeRecovery();
    }
  }

  public final void prepareRecovery() throws IOException { /*SKIP*/ }

  public final void recoverFP(long fp) throws IOException {
    Assert.check(!this.put(fp));
  }
  
  public final void completeRecovery() throws IOException { /*SKIP*/ }
  
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
