// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:30:03 PST by lamport
//      modified on Wed Nov 14 23:26:07 PST 2001 by yuanyu
//      modified on Wed Jun 28 12:00:16 PDT 2000 by rjoshi

package tlc2.tool;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.IOException;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.output.StatePrinter;
import tlc2.util.BufferedRandomAccessFile;
import tlc2.util.LongVec;
import util.FileUtil;
import util.ToolIO;

public class TLCTrace {

  private static String filename;
  private BufferedRandomAccessFile raf;
  private long lastPtr;
  private TraceApp tool;

  public TLCTrace(String metadir, String specFile, TraceApp tool)
  throws IOException {
    filename = metadir + FileUtil.separator + specFile + ".st";
    this.raf = new BufferedRandomAccessFile(filename, "rw");
    this.lastPtr = 1;
    this.tool = tool;
  }

  public final synchronized long writeState(long ploc, long fp)
  throws IOException {
    this.lastPtr = this.raf.getFilePointer();
    this.raf.writeLongNat(ploc);
    this.raf.writeLong(fp);
    return this.lastPtr;
  }

  public final void close() throws IOException {
    this.raf.close();
  }

  public synchronized long getPrev(long loc) throws IOException {
    this.raf.seek(loc);
    return this.raf.readLongNat();
  }

  public synchronized long getFP(long loc) throws IOException {
    this.raf.seek(loc);
    this.raf.readLongNat();    /*drop*/
    return this.raf.readLong();
  }

  public synchronized final int getLevel() throws IOException {
    long curLoc = this.raf.getFilePointer();
    int level = 0;
    for (long ploc = this.lastPtr; ploc != 1; ploc = this.getPrev(ploc)) {
      level++;
    }
    this.raf.seek(curLoc);
    return level;
  }

  public synchronized final int getLevel(long loc) throws IOException {
    long curLoc = this.raf.getFilePointer();
    int level = 0;
    for (long ploc = loc; ploc != 1; ploc = this.getPrev(ploc)) {
      level++;
    }
    this.raf.seek(curLoc);
    return level;
  }
  
  public final TLCStateInfo[] getTrace(long loc, boolean included)
  throws IOException {
    LongVec fps = new LongVec();

    synchronized(this) {
      long curLoc = this.raf.getFilePointer();
      long loc1 = (included) ? loc : this.getPrev(loc);
      for (long ploc = loc1; ploc != 1; ploc = this.getPrev(ploc)) {
	fps.addElement(this.getFP(ploc));
      }
      this.raf.seek(curLoc);
    }

    int stateNum = 0;
    int len = fps.size();
    TLCStateInfo[] res = new TLCStateInfo[len];
    if (len > 0) {
      long fp = fps.elementAt(len-1);
      TLCStateInfo sinfo = this.tool.getState(fp);
      if (sinfo == null) {
	ToolIO.err.println("Failed to recover the initial state from its fingerprint. This is probably a TLC bug(1).");
	System.exit(1);
      }
      res[stateNum++] = sinfo;
      for (int i = len - 2; i >= 0; i--) {
	fp = fps.elementAt(i);
	sinfo = this.tool.getState(fp, sinfo.state);
	if (sinfo == null) {
	  ToolIO.err.println("Failed to recover the state from its fingerprint. This is probably a TLC bug(2).");
	  System.exit(1);
	}
	res[stateNum++] = sinfo;
      }
    }
    return res;
  }

  /**
   * Write out a sequence of states that reaches s2 from an initial
   * state, according to the spec. s2 is a next state of s1.
   */
  public synchronized final void printTrace(long loc1, TLCState s1, TLCState s2)
  throws IOException, WorkerException 
  {
      MP.printError(EC.TLC_BEHAVIOR_UP_TO_THIS_POINT);
      // Print the prefix leading to s1:
      TLCState lastState = null;
      TLCStateInfo[] prefix = this.getTrace(loc1, false);
      int idx = 0;
      while (idx < prefix.length) 
      {
          StatePrinter.printState(prefix[idx], lastState, idx+1);
          lastState = prefix[idx].state;
          idx++;
      }

      // Print s1:
      TLCStateInfo sinfo;
      if (prefix.length == 0) {
          sinfo = this.tool.getState(s1.fingerPrint());
          if (sinfo == null) 
          {
              ToolIO.err.println("Failed to recover the initial state from its fingerprint. This is probably a TLC bug(3).");
              System.exit(1);
          }
      }
      else 
      {
          TLCState s0 = prefix[prefix.length-1].state;
          sinfo = this.tool.getState(s1.fingerPrint(), s0);
          if (sinfo == null) 
          {
              ToolIO.err.println("Failed to find the action that generated the following state. This is probably a TLC bug(4).");
              ToolIO.err.println(s1);      
              System.exit(1);
          }
      }
      if (s2 == null) 
      { 
          lastState = null; 
      }
      StatePrinter.printState(sinfo, lastState, ++idx);
      lastState = sinfo.state;

      // Print s2:
      if (s2 != null) {
          sinfo = this.tool.getState(s2, s1);
          if (sinfo == null) 
          {
              ToolIO.err.println("Failed to find the action to the following states. This is probably a TLC bug(5).");
              ToolIO.err.println(s2);      
              System.exit(1);
          }
          StatePrinter.printState(sinfo, null, ++idx);
      }
  }


  /**
   * SZ Jul 10, 2009: method not used 
   * Returns a sequence of states that reaches, but excludes the
   * state with fingerprint fp.
   */
  protected final TLCStateInfo[] printPrefix(long fp) throws IOException {
    // First, find the location for fp:
    this.raf.seek(0);
    this.raf.readLongNat();    /*drop*/

    while (this.raf.readLong() != fp) {
      this.raf.readLongNat();  /*drop*/
    }
    
    // Print the states corresponding to the fps:
    TLCState lastState = null;
    TLCStateInfo[] prefix = this.getTrace(this.lastPtr, false);
    int idx = 0;
    while (idx < prefix.length) {
        StatePrinter.printState(prefix[idx], lastState, idx+1);
      lastState = prefix[idx].state;
      idx++;
    }
    return prefix;
  }
  
  /* Checkpoint.  */
  public synchronized final void beginChkpt() throws IOException {
    this.raf.flush();
    // SZ Feb 24, 2009: FileUtil introduced
    DataOutputStream dos = FileUtil.newDFOS(filename + ".tmp");
    dos.writeLong(this.raf.getFilePointer());
    dos.writeLong(this.lastPtr);
    dos.close();
  }

  public final void commitChkpt() throws IOException {
    File oldChkpt = new File(filename + ".chkpt");
    File newChkpt = new File(filename + ".tmp");
    if ((oldChkpt.exists() && !oldChkpt.delete()) ||
	!newChkpt.renameTo(oldChkpt)) {
      throw new IOException("Trace.commitChkpt: cannot delete " + oldChkpt);
    }
  }

  public final void recover() throws IOException {
    // SZ Feb 24, 2009: FileUtil introduced
    DataInputStream dis = FileUtil.newDFIS(filename + ".chkpt");
    long filePos = dis.readLong();
    this.lastPtr = dis.readLong();
    dis.close();
    this.raf.seek(filePos);
  }

  public static String getFilename() { return filename; }

  public static long getRecoverPtr() throws IOException {
      // SZ Feb 24, 2009: FileUtil introduced
    DataInputStream dis = FileUtil.newDFIS(filename + ".chkpt");
    long res = dis.readLong();
    dis.close();
    return res;
  }

  public long[] addBlock(long fp[], long prev[]) throws IOException {
    // Reuse prev.
    for (int i = 0; i < fp.length; i++) {
      prev[i] = this.writeState(prev[i], fp[i]);
    }
    return prev;
  }

  public synchronized final Enumerator elements() throws IOException {
    return new Enumerator();
  }

  final class Enumerator {
    long len;
    BufferedRandomAccessFile enumRaf;
    
    Enumerator() throws IOException {
      this.len = raf.length();
      this.enumRaf = new BufferedRandomAccessFile(filename, "r");
    }

    final void reset(long pos) throws IOException {
      this.len = raf.length();
      if (pos == -1) {
	pos = this.enumRaf.getFilePointer();
      }
      this.enumRaf = new BufferedRandomAccessFile(filename, "r");
      this.enumRaf.seek(pos);
    }
    
    final long nextPos() {
      long fpos = this.enumRaf.getFilePointer();
      if (fpos < this.len) { return fpos; }
      return -1;
    }

    final long nextFP() throws IOException {
      this.enumRaf.readLongNat();    /*drop*/
      return this.enumRaf.readLong();
    }
  }

}
