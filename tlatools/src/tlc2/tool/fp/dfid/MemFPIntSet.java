// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp.dfid;

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
import util.WrongInvocationException;

/**
 * A <code>MemFPIntSet</code> is a subclass of <code>FPIntSet</code>
 * and a memory-based fingerprint set implementations.  As required by
 * <code>FPIntSet</code>, this class must guarantee that its methods
 * are thread-safe.
 */

public class MemFPIntSet extends FPIntSet {
  private String metadir;
  private String filename;

  /**
   * The load factor and initial capacity for the hashtable.
   */
  private static final int MaxLoad = 20;
  private static final int LogInitialCapacity = 16;

  /**
   * The hash table used to represent the set.
   */
  private int[][] table;

  /**
   * The total number of entries in the set.
   */
  private long count;

  /**
   * Rehashes the table when count exceeds this threshold.
   */
  private long threshold;
    
  /**
   * The bit-mask used in hashing fingerprints.  Relies on two assumptions:
   *  (1) table.length is a power of 2.
   *  (2) fingerprints are so random that extracting parts of their bits
   *      makes a good hash function.
   */
  private int mask;

  /* Constructs a new, empty FPSet.  */
  public MemFPIntSet() throws RemoteException {
    this(LogInitialCapacity, MaxLoad);
  }

  /* The following constructor is provided for test programs only. */
  public MemFPIntSet(int logInitialCapacity, int maxLoad) throws RemoteException {
    int initialCapacity = 1 << logInitialCapacity;
    this.count = 0;
    this.threshold = (initialCapacity * maxLoad);
    this.table = new int[initialCapacity][];
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
	size += 16 + (this.table[i].length * 4);
      }
    }
    return size;
  }

  public synchronized final void setLeveled(long fp) {
    int index = (int)(fp & this.mask);
    int[] list = this.table[index];

    // Test if the fingerprint is already in the hashtable.
    if (list != null) {
      int listlen = list.length;
      for (int i = 0; i < listlen; i += 3) {
	long fp1 = ((long)list[i] << 32) | ((long)list[i+1] & 0xFFFFFFFFL);
	if (fp1 == fp) {
	  list[i+2] = (list[i+2] & ~LeveledMask) | Leveled;
	  return;
	}
      }
    }

    throw new WrongInvocationException("MemFPIntSet.setLeveled: The fp must have been in the set.");
  }
  
  public synchronized final int setStatus(long fp, int status) {
    int index = (int)(fp & this.mask);
    int[] list = this.table[index];

    // Test if the fingerprint is already in the hashtable.
    if (list != null) {
      int listlen = list.length;
      for (int i = 0; i < listlen; i += 3) {
	long fp1 = ((long)list[i] << 32) | ((long)list[i+1] & 0xFFFFFFFFL);
	if (fp == fp1) {
	  int status1 = list[i+2];
	  list[i+2] = status1 | status;
	  // System.err.println("setStatus: " + fp + "  " + status1 + " -> " + this.getStatus(fp));
	  return status1;
	}
      }
    }

    if (count >= threshold) {
      // If the threshold is exceeded, rehash the table and recompute 
      // the index.
      this.rehash();
      index = (int)(fp & this.mask);
      list = this.table[index];
    } 

    // Creates the new entry.
    int len = (list == null ? 0 : list.length);
    int[] newList = new int[len+3];
    if (list != null) System.arraycopy(list, 0, newList, 0, len);
    newList[len] = (int)(fp >>> 32);
    newList[len+1] = (int)fp;
    newList[len+2] = (Level << 2) | Leveled | status;
    this.table[index] = newList;
    this.count++;
    // System.err.println("setStatus: " + fp + "  NEW -> " + this.getStatus(fp));
    return NEW;
  }

  public synchronized final int getStatus(long fp) {
    int index = (int)(fp & this.mask);
    int[] list = this.table[index];

    // Test if the fingerprint is already in the hashtable.
    if (list != null) {
      int listlen = list.length;
      for (int i = 0; i < listlen; i += 3) {
	long fp1 = ((long)list[i] << 32) | ((long)list[i+1] & 0xFFFFFFFFL);
	if (fp1 == fp) {
	  return list[i+2];
	}
      }
    }
    return NEW;
  }

  public final boolean allLeveled() {
    for (int i = 0; i < this.table.length; i++) {
      int[] bucket = this.table[i];
      if (bucket != null) {
	for (int j = 0; j < bucket.length; j += 3) {
	  if ((bucket[j+2] & LeveledMask) != Leveled) {
	    return false;
	  }
	}
      }
    }
    return true;
  }
  
  /**
   * Rehashes the contents of the hashtable into a hashtable with a 
   * larger capacity. This method is called automatically when the 
   * number of items in the hashtable exceeds this hashtable's capacity 
   * and load factor. 
   */
  private final void rehash() {
    long min = this.count, max = 0;
    int[][] oldTable = this.table;
    int oldCapacity = oldTable.length;
    int[][] newTable = new int[oldCapacity * 2][];
    final int onebitmask = oldCapacity;

    for (int i = 0; i < oldCapacity; i++) {
      int[] list = oldTable[i];
      if (list != null) {
	// The entries in list will be distributed over two arrays in
	// the new hash table.
	// count how big each list will be
	int cnt0 = 0;
	int cnt1 = 0;
	int listlen = list.length;
	if (listlen < min) min = listlen;
	if (listlen > max) max = listlen;
	for (int j = 0; j < listlen; j += 3) {
	  if ((list[j+1] & onebitmask) == 0)
	    cnt0 += 3;
	  else
	    cnt1 += 3;
	}
        	    
	// handle special cases if either list is empty
	if (cnt0 == 0) {
	  newTable[i+oldCapacity] = list;
	}
	else if (cnt1 == 0) {
	  newTable[i] = list;
	}
	else {
	  // allocate two new arrays
	  int[] list0 = new int[cnt0]; 
	  int[] list1 = new int[cnt1]; 
            	  
	  // copy the entries from the old list into the two new ones
	  for (int j = 0; j < listlen; j += 3) {
	    if ((list[j+1] & onebitmask) == 0) {
	      list0[cnt0-3] = list[j];
	      list0[cnt0-2] = list[j+1];
	      list0[cnt0-1] = list[j+2];
	      cnt0 -= 3;
	    }
	    else {
	      list1[cnt1-3] = list[j];
	      list1[cnt1-2] = list[j+1];
	      list1[cnt1-1] = list[j+2];
	      cnt1 -= 3;
	    }
	  }
            	    
	  // install new arrays in new table
	  newTable[i] = list0;
	  newTable[i+oldCapacity] = list1;
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
      int[] bucket = this.table[i];
      if (bucket != null) {
	for (int j = 0; j < bucket.length; j += 3) {
	  for (int k = j+3; k < bucket.length; k += 3) {
	    long x = ((long)bucket[j]) << 32 | bucket[j+1];
	    long y = ((long)bucket[k]) << 32 | bucket[k+1];
	    dis = Math.min(dis, Math.abs(x-y));
	  }
	  for (int k = i+1; k < this.table.length; k++) {
	    int[] bucket1 = this.table[k];
	    if (bucket1 != null) {
	      for (int m = 0; m < bucket1.length; m += 3) {
		long x = ((long)bucket[j]) << 32 | bucket[j+1];
		long y = ((long)bucket1[m]) << 32 | bucket1[m+1];
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
      int[] bucket = this.table[i];
      if (bucket != null) {
	for (int j = 0; j < bucket.length; j++) {
	  dos.writeInt(bucket[j]);
	}
      }
    }
    dos.close();
  }
      
  final public void beginChkpt() throws IOException {
    this.beginChkpt(this.filename);
  }

  final public void commitChkpt(String fname) throws IOException {
    File oldChkpt = new File(this.chkptName(fname, "chkpt"));
    File newChkpt = new File(this.chkptName(fname, "tmp"));
    if ((oldChkpt.exists() && !oldChkpt.delete()) ||
	!newChkpt.renameTo(oldChkpt)) {
      throw new IOException("MemFPIntSet.commitChkpt: cannot delete " + oldChkpt);
    }
  }
  
  final public void commitChkpt() throws IOException {
    this.commitChkpt(this.filename);
  }
    
  public final void recover(String fname) throws IOException {
    BufferedDataInputStream dis = 
      new BufferedDataInputStream(this.chkptName(fname, "chkpt"));
    try {
      while (!dis.atEOF()) {
	int fhi = dis.readInt();
	int flo = dis.readInt();
	int level = dis.readInt();

	if (count >= threshold) this.rehash();

	int index = (int)(flo & this.mask);
	int[] list = this.table[index];
	int len = (list == null ? 0 : list.length);
	int[] newList = new int[len+3];
	if (list != null) System.arraycopy(list, 0, newList, 0, len);
	newList[len] = fhi;
	newList[len+1] = flo;
	newList[len+2] = level;
	this.table[index] = newList;
	this.count++;
      }
    }
    catch (EOFException e) 
    {
      Assert.fail(EC.SYSTEM_DISK_IO_ERROR_FOR_FILE, "checkpoints");
    }
    dis.close();
  }
  
  final public void recover() throws IOException {
    this.recover(this.filename);
  }
    
  final private String chkptName(String fname, String ext) {
    return this.metadir + FileUtil.separator + fname + ".fp." + ext;
  }

}
