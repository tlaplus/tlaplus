// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import java.io.EOFException;
import java.io.File;
import java.io.IOException;
import java.net.InetAddress;
import java.rmi.RemoteException;

import tlc2.output.EC;
import tlc2.output.MP;
import util.Assert;
import util.BufferedDataInputStream;
import util.BufferedDataOutputStream;
import util.FileUtil;

/**
 * A <code>MemFPSet</code> is a subclass of <code>FPSet</code> and a
 * memory-based fingerprint set implementations. 
 * As required by <code>FPSet</code>, this class must guarantee that
 * its methods are thread-safe.
 */

public class MemFPSet extends FPSet {
  private String metadir;
  private String filename;

  /**
   * The load factor and initial capacity for the hashtable.
   */
  private static final int MaxLoad = 20;
  private static final int LogInitialCapacity = 16;

  /* The hash table used to represent the set.  */
  private long[][] table;

  /* The total number of entries in the set.   */
  private long count;

  /* Rehashes the table when count exceeds this threshold.  */
  private long threshold;
    
  /**
   * The bit-mask used in hashing fingerprints.  Relies on two assumptions:
   *  (1) table.length is a power of 2.
   *  (2) fingerprints are so random that extracting parts of their bits
   *      makes a good hash function.
   */
  private int mask;

  public MemFPSet() throws RemoteException {
	  this(new FPSetConfiguration());
  }
  
  /* Constructs a new, empty FPSet.  */
  public MemFPSet(final FPSetConfiguration fpSetConfig) throws RemoteException {
	super(fpSetConfig);
    int initialCapacity = 1 << LogInitialCapacity;
    this.count = 0;
    this.threshold = (initialCapacity * MaxLoad);
    this.table = new long[initialCapacity][];
    this.mask = initialCapacity - 1;
  }

  public final void init(int numThreads, String metadir, String filename) {
    this.metadir = metadir;
    this.filename = filename;
  }
    
  /**
   * Returns the number of fingerprints in this set.
   * @return  the number of fingerprints in this set.
   */
  public final synchronized long size() { return this.count; }

  public final synchronized long sizeof() {
    long size = 28; // 8 (ptr table) + 8 (long count) + 8 (long threshold) + 4 (int mask)
    size += 16 + (this.table.length * 8); // for this.table
    for (int i = 0; i < this.table.length; i++) {
      if (this.table[i] != null) {
	size += 16 + (this.table[i].length * 8);
      }
    }
    return size;
  }

  /**
   * Tests if the specified fingerprint is in this set.  As a side
   * effect, updates the set to contain the fingerprint.
   * 
   * @param   fp    the fingerprint.
   * @return  <code>true</code> if the specified fingerprint is 
   in this set; <code>false</code> otherwise.
   * <p>
   */
  public synchronized boolean put(long fp) {
    int index = (int)(fp & this.mask);
    long[] list = this.table[index];

    // Test if the fingerprint is already in the hashtable.
    if (list != null) {
      int listlen = list.length;
      for (int i = 0; i < listlen; i++) {
	if (list[i] == fp) return true;
      }
    }

    if (count >= threshold) {
      // If the threshold is exceeded, rehash the table and
      // recompute the index.
      rehash();
      index = (int)(fp & this.mask);
      list = this.table[index];
    } 

    // Creates the new entry.
    int len = (list == null ? 0 : list.length);
    long[] newList = new long[len+1];
    if (list != null) System.arraycopy(list, 0, newList, 0, len);
    newList[len] = fp;
    this.table[index] = newList;
	    
    this.count++;
    return false;
  }

  public synchronized boolean contains(long fp) {
    int index = (int)(fp & this.mask);
    long[] list = this.table[index];

    // Test if the fingerprint is already in the hashtable.
    if (list != null) {
      int listlen = list.length;
      for (int i = 0; i < listlen; i++) {
	if (list[i] == fp) return true;
      }
    }
    return false;
  }

  /**
   * Rehashes the contents of the hashtable into a hashtable with a
   * larger capacity. This method is called automatically when the
   * number of items in the hashtable exceeds this hashtable's
   * capacity and load factor.
   */
  private final void rehash() {
    long min = this.count, max = 0;
    long[][] oldTable = this.table;
    int oldCapacity = oldTable.length;
    long[][] newTable = new long[oldCapacity * 2][];
    final int onebitmask = oldCapacity;

    for (int i = 0; i < oldCapacity; i++) {
      long[] list = oldTable[i];
      if (list != null) {
	// The entries in list will be distributed over two arrays in
	// the new hash table.
	// count how big each list will be
	int cnt0 = 0;
	int cnt1 = 0;
	int listlen = list.length;
	if (listlen < min) min = listlen;
	if (listlen > max) max = listlen;
	for (int j = 0; j < listlen; j++) {
	  if ((list[j] & onebitmask) == 0)
	    cnt0++;
	  else
	    cnt1++;
	}
        	    
	// handle special cases if either list is empty
	if (cnt0 == 0) {
	  newTable[i + oldCapacity] = list;
	}
	else if (cnt1 == 0) {
	  newTable[i] = list;
	}
	else {
	  // allocate two new arrays
	  long[] list0 = new long[cnt0]; 
	  long[] list1 = new long[cnt1]; 
            	  
	  // copy the entries from the old list into the two new ones
	  for (int j = 0; j < listlen; j++) {
	    if ((list[j] & onebitmask) == 0) 
	      list0[--cnt0] = list[j];
	    else
	      list1[--cnt1] = list[j];
	  }
            	    
	  // install new arrays in new table
	  newTable[i] = list0;
	  newTable[i + oldCapacity] = list1;
	}
      }
    }
    this.threshold *= 2;
    this.table = newTable;
    this.mask = newTable.length - 1;
  }

  public final void exit(boolean cleanup) throws IOException {
    if (cleanup) {
      // Delete the metadata directory:
      File file = new File(this.metadir);
      FileUtil.deleteDir(file, true);
    }
    String hostname = InetAddress.getLocalHost().getHostName();    
    MP.printMessage(EC.TLC_FP_COMPLETED, hostname);
    System.exit(0);    
  }

  public final double checkFPs() {
    long dis = Long.MAX_VALUE;
    for (int i = 0; i < this.table.length; i++) {
      long[] bucket = this.table[i];
      if (bucket != null) {
	for (int j = 0; j < bucket.length; j++) {
	  for (int k = j+1; k < bucket.length; k++) {
	    dis = Math.min(dis, Math.abs(bucket[j]-bucket[k]));
	  }
	  for (int k = i+1; k < this.table.length; k++) {
	    long[] bucket1 = this.table[k];
	    if (bucket1 != null) {
	      for (int m = 0; m < bucket1.length; m++) {
		long x = bucket[j];
		long y = bucket1[m];
		long dis1 = (x > y) ? x-y : y-x;
		if (dis1 >= 0) {
		  dis = Math.min(dis, dis1);
		}
	      }
	    }
	  }
	}
      }
    }
    return (1.0/dis);
  }

  // Checkpoint.
  public final void beginChkpt(String fname) throws IOException {
    BufferedDataOutputStream dos =
      new BufferedDataOutputStream(this.chkptName(fname, "tmp"));
    for (int i = 0; i < this.table.length; i++) {
      long[] bucket = this.table[i];
      if (bucket != null) {
	for (int j = 0; j < bucket.length; j++) {
	  dos.writeLong(bucket[j]);
	}
      }
    }
    dos.close();
  }
      
  final public void commitChkpt(String fname) throws IOException {
    File oldChkpt = new File(this.chkptName(fname, "chkpt"));
    File newChkpt = new File(this.chkptName(fname, "tmp"));
    if ((oldChkpt.exists() && !oldChkpt.delete()) ||
	!newChkpt.renameTo(oldChkpt)) {
      throw new IOException("MemFPSet.commitChkpt: cannot delete " + oldChkpt);
    }
  }
  
  public final void recover(String fname) throws IOException {
    BufferedDataInputStream dis = 
      new BufferedDataInputStream(this.chkptName(fname, "chkpt"));
    try {
      while (!dis.atEOF()) {
          Assert.check(!this.put(dis.readLong()), EC.TLC_FP_NOT_IN_SET);
      }
    }
    catch (EOFException e) {
      Assert.fail(EC.SYSTEM_DISK_IO_ERROR_FOR_FILE, "checkpoints");
    }
    dis.close();
  }
  
  final public void beginChkpt() throws IOException {
    this.beginChkpt(this.filename);
  }

  final public void commitChkpt() throws IOException {
    this.commitChkpt(this.filename);
  }
    
  final public void recover() throws IOException {
    this.recover(this.filename);
  }

  public final void prepareRecovery() throws IOException { /*SKIP*/ }

  public final void recoverFP(long fp) throws IOException {
    Assert.check(!this.put(fp), EC.TLC_FP_NOT_IN_SET);
  }
  
  public final void completeRecovery() throws IOException { /*SKIP*/ }
    
  final private String chkptName(String fname, String ext) {
    return this.metadir + FileUtil.separator + fname + ".fp." + ext;
  }

}
