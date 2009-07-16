// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:28 PST by lamport  
//      modified on Tue Jan  8 23:38:34 PST 2002 by yuanyu   

package tlc2.util;

import java.io.File;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

import tlc2.output.EC;
import util.Assert;
import util.FileUtil;

/**
 * Alternative implementation
 * not used currently
 * @version $Id$
 */
public class DiskObjectStack extends ObjectStack {
  private final static int BufSize = 8192;

  /**
   * Invariants:
   * I1. Entries in buf1 are in the indices: [0, index1)
   * I2. Entries in buf2 are in the indices: [0, index2)
   * I3. /\ 0 <= index <= buf.length
   *     /\ index == 0 => buffer empty
   *     /\ index == buf.length => buffer full
   */
    
  /* Fields */
  private final String filePrefix;
  protected Object[] buf1, buf2, buf;
  protected int index;
  protected ObjectPoolStack diskStack;
  
  /* Constructors */
  public DiskObjectStack(String diskdir, String name) {
    this.buf1 = new Object[BufSize];
    this.buf2 = new Object[BufSize];
    this.buf = this.buf1;
    this.index = 0;
    this.filePrefix = diskdir + FileUtil.separator + name;
    this.diskStack = new ObjectPoolStack(BufSize, this.filePrefix);
  }
  
  final void enqueueInner(Object state) {
    if (this.index == BufSize && this.buf == this.buf2) {
      // need to flush buf1 to disk      
      try {
	this.buf = this.diskStack.write(this.buf1);
	this.buf1 = this.buf2;
	this.buf2 = this.buf;
	this.index = 0;
      }
      catch (Exception e) {
          Assert.fail(EC.SYSTEM_ERROR_WRITING_STATES, new String[]{"stack", e.getMessage()});      
      }
    }
    this.buf[this.index++] = state;
  }
  
  final Object dequeueInner() {
    if (this.buf == this.buf1 && this.index < BufSize/2) {
      // need to fill buffers
      try {
	Object[] tempBuf = this.diskStack.read(this.buf);
	if (tempBuf != null) {
	  this.buf2 = this.buf1;
	  this.buf1 = tempBuf;
	  this.buf = this.buf2;
	}
      }
      catch (Exception e) {
	Assert.fail(EC.SYSTEM_ERROR_READING_STATES, new String[]{"stack", e.getMessage()});
      }
    }
    return this.buf[--this.index];
  }

  /* Checkpoint.  */
  public final void beginChkpt() throws IOException {
    String filename = this.filePrefix + ".tmp";
    ObjectOutputStream oos = FileUtil.newOBFOS(filename);
    oos.writeInt(this.len);
    int index1 = (this.buf == this.buf1) ? this.index : BufSize;
    int index2 = (this.buf == this.buf1) ? 0 : this.index;
    oos.writeInt(index1);
    oos.writeInt(index2);
    for (int i = 0; i < index1; i++) {
      oos.writeObject(this.buf1[i]);
    }
    for (int i = 0; i < index2; i++) {
      oos.writeObject(this.buf2[i]);
    }
    oos.close();
  }

  public final void commitChkpt() throws IOException {
    // SZ 23.02.2009: filename is not used  
    // String filename = this.filePrefix + ".chkpt"; 
    File oldChkpt = new File(this.filePrefix + ".chkpt");
    File newChkpt = new File(this.filePrefix + ".tmp");
    if ((oldChkpt.exists() && !oldChkpt.delete()) ||
	!newChkpt.renameTo(oldChkpt)) {
      String msg = "DiskObjectStack.commitChkpt: cannot delete " + oldChkpt;
      throw new IOException(msg);
    }
  }

  public final void recover() throws IOException {
    String filename = this.filePrefix + ".chkpt";
    
    ObjectInputStream ois = FileUtil.newOBFIS(filename);
    this.len = ois.readInt();
    int index1 = ois.readInt();
    int index2 = ois.readInt();
    try {
      for (int i = 0; i < index1; i++) {
	this.buf1[i] = ois.readObject();
      }
      for (int i = 0; i < index2; i++) {
	this.buf2[i] = ois.readObject();
      }
    }
    catch (ClassNotFoundException e) {
        Assert.fail(EC.SYSTEM_CHECKPOINT_RECOVERY_CORRUPT, e.getMessage());
    }
    finally {
      ois.close();
    }
    if (index2 == 0) {
      this.buf = this.buf1;
      this.index = index1;
    }
    else {
      this.buf = this.buf2;
      this.index = index2;
    }
  }
  
}
