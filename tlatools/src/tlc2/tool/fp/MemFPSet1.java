// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:15:06 PST by lamport
//      modified on Tue May 15 23:11:51 PDT 2001 by yuanyu

package tlc2.tool.fp;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.IOException;
import java.net.InetAddress;
import java.rmi.RemoteException;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.util.SetOfLong;
import util.Assert;
import util.FileUtil;

/**
 * Alternative implementation
 * @deprecated not used currently
 * @version $Id$
 */
public final class MemFPSet1 extends FPSet {
  private String metadir;
  private String filename;
  private SetOfLong set;

  public MemFPSet1(final FPSetConfiguration fpSetConfig) throws RemoteException {
    super(fpSetConfig);
    this.set = new SetOfLong(10001, 0.75f);
  }

  public final void init(int numThreads, String metadir, String filename) {
    this.metadir = metadir;
    this.filename = filename;
  }

  public final long size() { return this.set.size(); }

  public final long sizeof() { return 8 + this.set.sizeof(); }

  public synchronized final boolean put(long fp) {
    return this.set.put(fp);
  }

  public synchronized final boolean contains(long fp) {
    return this.set.contains(fp);
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

  public final double checkFPs() { return this.set.checkFPs(); }

  /* Checkpoint. */
  public final void beginChkpt(String fname) throws IOException {
    DataOutputStream dos = FileUtil.newDFOS(this.chkptName(fname, "tmp"));
    this.set.beginChkpt(dos);
    dos.close();
  }
  
  public final void commitChkpt(String fname) throws IOException {
    File oldChkpt = new File(this.chkptName(fname, "chkpt"));
    File newChkpt = new File(this.chkptName(fname, "tmp"));
    if ((oldChkpt.exists() && !oldChkpt.delete()) ||
	!newChkpt.renameTo(oldChkpt)) {
      throw new IOException("MemFPSet1.commitChkpt: cannot delete " + oldChkpt);
    }
  } 

  public final void recover(String fname) throws IOException {
    
    DataInputStream dis = FileUtil.newDFIS(this.chkptName(fname, "chkpt"));
    this.set.recover(dis);
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
    Assert.check(!this.set.put(fp), EC.TLC_FP_NOT_IN_SET);
  }
  
  public final void completeRecovery() throws IOException { /*SKIP*/ }

  private final String chkptName(String fname, String ext) {
    return this.metadir + FileUtil.separator + fname + ".fp." + ext;
  }
  
}
