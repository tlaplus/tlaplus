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
 * <code>MemFPSet2</code> is a subclass of {@link MemFPSet} that
 * implements a fingerprint set as a hashtable with a central spine
 * and collision buckets.
 * <P>
 * This class recognizes the following attribute in its
 * <code>alist</code> argument:
 * <PRE>
 * Name          Type     Default  Legal range  Meaning
 * ------------  -------  -------  -----------  ---------------------------------
 * LogSpineSize  Integer  24       [24 .. 30]   Log of size of hash table's spine
 * </PRE>
 * <P>
 * Collision buckets are implemented as arrays that are grown on
 * demand, one entry at a time.  The last 3 bytes of each fingerprint
 * is encoded in the bucket index, leaving 5 bytes to be stored in the
 * buckets.  Under the Compaq JVM with the <I>-fast64</I> flag,
 * pointers are 8 bytes long, and the overhead per array is 16 bytes
 * (8 bytes object overhead, 4 bytes padding, and 4 bytes for the
 * length field).  Assuming a spine size of 2<SUP>24</SUP>, the cost
 * of storing 2<SUP>30</SUP> fingerprints is 5.375 GB.
 */

public final class MemFPSet2 extends FPSet {
    private String metadir;
    private String filename;
  
    /* The hash table used to represent the set. */
    private byte[][] table;
    //@ invariant table.length > 0
    /*@ invariant (forall int i; 0 <= i & i < table.length ==>
            table[i] == null | (table[i].length / 5) * 5 ==  table[i].length) */
    
    /* The total number of entries in the set. */
    private long count;

    /* The bit-mask used in hashing fingerprints. Relies on two assumptions:
       <OL>
       <LI> <code>table.length</code> is a power of 2
       <LI> fingerprints are so random that extracting parts of their bits
            makes a good hash function.
       </OL>
     */
    private int mask;
    //@ invariant mask == table.length - 1

    private int LogSpineSize = 24;
  
  /* Constructs a new, empty FPSet. */
  public MemFPSet2(final FPSetConfiguration fpSetConfig) throws RemoteException {
	super(fpSetConfig);
    int spineSize = 1 << LogSpineSize;
    this.count = 0;
    this.table = new byte[spineSize][];
    this.mask = spineSize - 1;
  }
  
  public void init(int numThreads, String metadir, String fname) {
    this.metadir = metadir;
    this.filename = metadir + FileUtil.separator + fname;
  }

  public synchronized final long size() { return this.count; }
    
  public synchronized final boolean put(long fp) {
        int index = (int)(fp & this.mask);
        byte[] bucket = this.table[index];
        byte b1 = (byte)((fp >>> 24) & 0xffL);
        byte b2 = (byte)((fp >>> 32) & 0xffL);
        byte b3 = (byte)((fp >>> 40) & 0xffL);
        byte b4 = (byte)((fp >>> 48) & 0xffL);
        byte b5 = (byte)((fp >>> 56) & 0xffL);
        // Test if the fingerprint is already in the hashtable.
        int len = bucket == null ? 0 : bucket.length;
        for (int i = 0; i < len; i += 5) {
            if (bucket[i  ] == b1 && 
                bucket[i+1] == b2 && 
                bucket[i+2] == b3 && 
                bucket[i+3] == b4 && 
                bucket[i+4] == b5) return true;
        }
        // bucket is full 
        byte[] newBucket = new byte[len + 5];
        if (bucket != null) System.arraycopy(bucket, 0, newBucket, 0, len);
        this.table[index] = newBucket;
        newBucket[len  ] = b1;
        newBucket[len+1] = b2;
        newBucket[len+2] = b3;
        newBucket[len+3] = b4;
        newBucket[len+4] = b5;
        this.count++;
        return false;
  }

  public synchronized final boolean contains(long fp) {
    int index = (int)(fp & this.mask);
    byte[] bucket = this.table[index];
    byte b1 = (byte)((fp >>> 24) & 0xffL);
    byte b2 = (byte)((fp >>> 32) & 0xffL);
    byte b3 = (byte)((fp >>> 40) & 0xffL);
    byte b4 = (byte)((fp >>> 48) & 0xffL);
    byte b5 = (byte)((fp >>> 56) & 0xffL);
    // Test if the fingerprint is already in the hashtable.
    int len = bucket == null ? 0 : bucket.length;
    for (int i = 0; i < len; i += 5) {
      if (bucket[i  ] == b1 && 
	  bucket[i+1] == b2 && 
	  bucket[i+2] == b3 && 
	  bucket[i+3] == b4 && 
	  bucket[i+4] == b5) return true;
    }
    return false;
  }

  public final void exit(boolean cleanup) throws IOException {
    if (cleanup) {
      // Delete the metadata directory:
      FileUtil.deleteDir(this.metadir, true);
    }
    String hostname = InetAddress.getLocalHost().getHostName();    
    MP.printMessage(EC.TLC_FP_COMPLETED, hostname);
    System.exit(0);    
  }

  public final double checkFPs() {
    long dis = Long.MAX_VALUE;
    for (int i = 0; i < this.table.length; i++) {
      long low = i & 0xffffffL;	
      byte[] bucket = this.table[i];
      if (bucket != null) {
	int j = 0;
	while (j < bucket.length) {
	  long b1 = (bucket[j++] & 0xffL) << 24;
	  long b2 = (bucket[j++] & 0xffL) << 32;
	  long b3 = (bucket[j++] & 0xffL) << 40;
	  long b4 = (bucket[j++] & 0xffL) << 48;
	  long b5 = (bucket[j++] & 0xffL) << 56;
	  long fp = b5 | b4 | b3 | b2 | b1 | low;
	  int k = j;
	  while (k < bucket.length) {
	    b1 = (bucket[k++] & 0xffL) << 24;
	    b2 = (bucket[k++] & 0xffL) << 32;
	    b3 = (bucket[k++] & 0xffL) << 40;
	    b4 = (bucket[k++] & 0xffL) << 48;
	    b5 = (bucket[k++] & 0xffL) << 56;
	    long fp1 = b5 | b4 | b3 | b2 | b1 | low;
	    long dis1 = (fp > fp1) ? fp-fp1 : fp1-fp;
	    if (dis1 >= 0) {
	      dis = Math.min(dis, dis1);
	    }
	  }
	  for (k = i+1; k < this.table.length; k++) {
	    byte[] bucket1 = this.table[k];
	    if (bucket1 != null) {
	      long low1 = k & 0xffffffL;
	      int k1 = 0;
	      while (k1 < bucket.length) {
		b1 = (bucket[k1++] & 0xffL) << 24;
		b2 = (bucket[k1++] & 0xffL) << 32;
		b3 = (bucket[k1++] & 0xffL) << 40;
		b4 = (bucket[k1++] & 0xffL) << 48;
		b5 = (bucket[k1++] & 0xffL) << 56;
		long fp1 = b5 | b4 | b3 | b2 | b1 | low1;
		long dis1 = (fp > fp1) ? fp-fp1 : fp1-fp;
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

  public final void beginChkpt(String fname) throws IOException {
    BufferedDataOutputStream dos =
      new BufferedDataOutputStream(this.chkptName(fname, "tmp"));
    for (int i = 0; i < this.table.length; i++) {
      long low = i & 0xffffffL;
      byte[] bucket = this.table[i];
      if (bucket != null) {
	int j = 0;
	while (j < bucket.length) {
	  long b1 = (bucket[j++] & 0xffL) << 24;
	  long b2 = (bucket[j++] & 0xffL) << 32;
	  long b3 = (bucket[j++] & 0xffL) << 40;
	  long b4 = (bucket[j++] & 0xffL) << 48;
	  long b5 = (bucket[j++] & 0xffL) << 56;
	  long fp = b5 | b4 | b3 | b2 | b1 | low;
	  dos.writeLong(fp);
	}
      }
    }
    dos.close();
  }

  final public void commitChkpt(String fname) throws IOException {
    File oldChkpt = new File(this.chkptName(fname, "chkpt"));
    File newChkpt = new File(this.chkptName(fname, "tmp"));
    if ((oldChkpt.exists() && !oldChkpt.delete()) ||
	!newChkpt.renameTo(oldChkpt)) 
    {
      throw new IOException("MemFPSet2.commitChkpt: cannot delete " + oldChkpt);
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
    catch (EOFException e) 
    {
        throw new IOException("MemFPSet2.recover: failed.");
    }
    dis.close();
  }

  public final void beginChkpt() throws IOException {
    this.beginChkpt(this.filename);
  }

  public final void commitChkpt() throws IOException {
    this.commitChkpt(this.filename);
  }

  public final void recover() throws IOException {
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
