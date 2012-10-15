// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:12:32 PST by lamport
//      modified on Tue May 15 11:44:57 PDT 2001 by yuanyu

package tlc2.tool.fp.dfid;

import java.io.IOException;
import java.rmi.RemoteException;

/**
 * <b>Note:</b> All concrete subclasses of this class are required to
 * guarantee that their methods are thread-safe.
 * @version $Id$
 */
public abstract class FPIntSet
// SZ Jul 13, 2009: there is no reason to extend the RMI interfaces, since they are not used
// extends UnicastRemoteObject implements FPIntSetRMI 
{

  public static int Port = 10998;   // port # for fpset server

  protected FPIntSet() throws RemoteException { /*SKIP*/ }
  
  /**
   * Performs any initialization necessary to handle "numThreads"
   * worker threads and one main thread. Subclasses will need to
   * override this method as necessary. This method must be called
   * after the constructor but before any of the other methods below.
   */
  public abstract void init(int numThreads, String metadir, String filename)
  throws IOException;
    
  /* Returns the number of fingerprints in this set. */
  public abstract long size();
    
  /**
   * We use two bits to record the status of a fp: one DONE bit and
   * one Leveled bit.  The remaining 30 bits are used for level.
   */
  public static final int SBits = 2;
  public static final int LBits = 30;

  public static final int SBitsMask = 0x3;
  public static final int DoneMask = 0x1;
  public static final int LeveledMask = 0x2;

  public static final int NEW = 0;
  public static final int DONE = 1;
  
  
  /* 
   * SZ Mar 9, 2009: These variables seem to be used in the following way.
   * 
   * An instance of FPIntSet is hold by every worker. In addition, a "global" FPIntSet is used in the ModelChecker.
   * The static fields are used to compare the "global" value with the instance values of the worker instances.
   * This is a very fishy, and should be changed to the following: static modifiers should be removed and replaced by explicit
   * comparison with the instance variable controlled by the model checker 
   */
  protected static int Level = 1;
  protected static int Leveled = 0;

  public static void incLevel() {
    Level++;
    Leveled = 2 - Leveled;
  }

  public static boolean isCompleted(int status) {
    return (((status & LeveledMask) == Leveled) ||
	    ((status & DoneMask) == DONE));
  }

  public static boolean isDone(int status) {
    return (status & DoneMask) == DONE;
  }
  
  public static int getLevel(int status) {
    return status >>> SBits;
  }

  public static boolean isLeaf(int status) {
    return status == NEW || (status >>> SBits) == Level;
  }
  
  /**
   * Set fp to be leveled, which means that there is no need to
   * explore fp again at this level.
   */
  public abstract void setLeveled(long fp);
  
  /**
   * Set the status of fp to status. It does nothing if the status of
   * fp in this is already higher than status.  This method will not
   * change the Leveled bit.
   *
   * The return value is an integer:
   *   - if fp was not in the set, returns NEW.
   *   - if fp was in the set, returns the old 3-bit status.
   *
   * NOTE: The methods setStatus and getStatus can be used together.
   * They can not be used with the methods put and contains.
   */
  public abstract int setStatus(long fp, int status);

  /**
   * Returns the current 3-bit status of fp.  If fp is not in the set,
   * returns NEW.
   */
  public abstract int getStatus(long fp);  
  
  public abstract boolean allLeveled();

  public void close() { /*SKIP*/ }

  public void addThread() throws IOException { /*SKIP*/ }
  
  public abstract void exit(boolean cleanup) throws IOException;

  public abstract double checkFPs() throws IOException;

  public abstract void beginChkpt() throws IOException;
  public abstract void commitChkpt() throws IOException;
  public abstract void recover() throws IOException;

  /* The set of checkpoint methods for remote checkpointing. */  
  public abstract void beginChkpt(String filename) throws IOException;
  public abstract void commitChkpt(String filename) throws IOException;
  public abstract void recover(String filename) throws IOException;
  
// SZ Jul 10, 2009: main method that could have been used during the RMI tests
// removed since it is dead code now
//  public static void main(String args[]) {
//    ToolIO.out.println("TLC FP Server " + TLCGlobals.versionOfTLC);
//
//    String metadir = null;
//    String fromChkpt = null;
//    int index = 0;
//    while (index < args.length) {
//      if (args[index].charAt(0) == '-') {
//	printErrorMsg("Error: unrecognized option: " + args[index]);
//	System.exit(0);
//      }
//      if (metadir != null) {
//	printErrorMsg("Error: more than one directory for metadata: " + metadir +
//		      " and " + args[index]);
//	System.exit(0);
//      }
//      metadir = args[index++] + FileUtil.separator;
//    }
//
//    String hostname = "Unknown";
//    try {
//      hostname = InetAddress.getLocalHost().getHostName();
//      metadir = (metadir == null) ? hostname : (metadir + hostname);
//      File filedir = new File(metadir);
//      if (!filedir.exists()) {
//	boolean created = filedir.mkdirs();
//	if (!created) {
//	  System.err.println("Error: fingerprint server could not make a directory" +
//			     " for the disk files it needs to write.\n");
//	  System.exit(0);
//	}
//      }
//      // Start memory-based fingerprint set server.
//      // Note: It would be wrong to use the disk-based implementation.
//      FPIntSet fpSet = new MemFPIntSet();
//      fpSet.init(1, metadir, "fpset");
//      if (fromChkpt != null) {
//	fpSet.recover();    // recover when instructed
//      }
//      Registry rg = LocateRegistry.createRegistry(Port);
//      rg.rebind("FPSetServer", fpSet);
//      System.out.println("Fingerprint set server at " + hostname + " is ready.");
//
//      synchronized(fpSet) {
//	while (true) {
//	    System.out.println("Progress: The number of fingerprints stored at " +
//			     hostname + " is " + fpSet.size() + ".");
//	  fpSet.wait(300000);	  
//	}
//      }
//    }
//    catch (Exception e) {
//        System.err.println(hostname + ": Error: " + e.getMessage());
//    }
//  }

//  private static void printErrorMsg(String msg) {
//      System.err.println(msg);
//      System.err.println("Usage: java tlc2.tool.FPSet [-option] metadir");
//  }

}
