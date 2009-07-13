// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:13:19 PST by lamport
//      modified on Tue May 15 11:44:57 PDT 2001 by yuanyu

package tlc2.tool;

import java.io.IOException;
import java.rmi.RemoteException;

import tlc2.util.BitVector;
import tlc2.util.LongVec;

/**
 * An <code>FPSet</code> is a set of 64-bit fingerprints.
 *
 * Note: All concrete subclasses of this class are required to
 * guarantee that their methods are thread-safe.
 */

public abstract class FPSet
// SZ Jul 13, 2009: RMI is not used 
//extends UnicastRemoteObject implements FPSetRMI
{

    protected FPSet() throws RemoteException
    { /*SKIP*/
    }

    /**
     * Performs any initialization necessary to handle "numThreads"
     * worker threads and one main thread. Subclasses will need to
     * override this method as necessary. This method must be called
     * after the constructor but before any of the other methods below.
     */
    public abstract void init(int numThreads, String metadir, String filename) throws IOException;

    /* Returns the number of fingerprints in this set. */
    public abstract long size();

    /**
     * Returns <code>true</code> iff the fingerprint <code>fp</code> is
     * in this set. If the fingerprint is not in the set, it is added to
     * the set as a side-effect.
     */
    public abstract boolean put(long fp) throws IOException;

    /**
     * Returns <code>true</code> iff the fingerprint <code>fp</code> is
     * in this set.
     */
    public abstract boolean contains(long fp) throws IOException;

    public void close()
    { /*SKIP*/
    }

    public void addThread() throws IOException
    { /*SKIP*/
    }

    public abstract void exit(boolean cleanup) throws IOException;

    public abstract double checkFPs() throws IOException;

    public abstract void beginChkpt() throws IOException;

    public abstract void commitChkpt() throws IOException;

    public abstract void recover() throws IOException;

    public abstract void recoverFP(long fp) throws IOException;

    public abstract void prepareRecovery() throws IOException;

    public abstract void completeRecovery() throws IOException;

    /* The set of checkpoint methods for remote checkpointing. */
    public abstract void beginChkpt(String filename) throws IOException;

    public abstract void commitChkpt(String filename) throws IOException;

    public abstract void recover(String filename) throws IOException;

    public final BitVector putBlock(LongVec fpv) throws IOException
    {
        BitVector bv = new BitVector(fpv.size());
        for (int i = 0; i < fpv.size(); i++)
        {
            if (!this.put(fpv.elementAt(i)))
            {
                bv.set(i);
            }
        }
        return bv;
    }

    public final BitVector containsBlock(LongVec fpv) throws IOException
    {
        BitVector bv = new BitVector(fpv.size());
        for (int i = 0; i < fpv.size(); i++)
        {
            if (!this.contains(fpv.elementAt(i)))
            {
                bv.set(i);
            }
        }
        return bv;
    }

    // SZ Jul 10, 2009: this method is not used
//    public static void main(String args[])
//    {
//        System.out.println("TLC FP Server " + TLCGlobals.versionOfTLC);
//
//        String metadir = null;
//        String fromChkpt = null;
//        int index = 0;
//        while (index < args.length)
//        {
//            if (args[index].charAt(0) == '-')
//            {
//                printErrorMsg("Error: unrecognized option: " + args[index]);
//                System.exit(0);
//            }
//            if (metadir != null)
//            {
//                printErrorMsg("Error: more than one directory for metadata: " + metadir + " and " + args[index]);
//                System.exit(0);
//            }
//            metadir = args[index++] + FileUtil.separator;
//        }
//
//        String hostname = "Unknown";
//        try
//        {
//            hostname = InetAddress.getLocalHost().getHostName();
//            metadir = (metadir == null) ? hostname : (metadir + hostname);
//            File filedir = new File(metadir);
//            if (!filedir.exists())
//            {
//                boolean created = filedir.mkdirs();
//                if (!created)
//                {
//                    System.err
//                            .println("Error: fingerprint server could not make a directory for the disk files it needs to write.\n");
//                    System.exit(0);
//                }
//            }
//            // Start memory-based fingerprint set server.
//            // Note: It would be wrong to use the disk-based implementation.
//            FPSet fpSet = new MemFPSet2();
//            fpSet.init(1, metadir, "fpset");
//            if (fromChkpt != null)
//            {
//                fpSet.recover(); // recover when instructed
//            }
//            Registry rg = LocateRegistry.createRegistry(Port);
//            rg.rebind("FPSetServer", fpSet);
//            System.out.println("Fingerprint set server at " + hostname + " is ready.");
//
//            synchronized (fpSet)
//            {
//                while (true)
//                {
//                    System.out.println("Progress: The number of fingerprints stored at " + hostname + " is "
//                            + fpSet.size() + ".");
//                    fpSet.wait(300000);
//                }
//            }
//        } catch (Exception e)
//        {
//            System.out.println(hostname + ": Error: " + e.getMessage());
//        }
//    }
//    private static void printErrorMsg(String msg)
//    {
//        System.out.println(msg);
//        System.out.println("Usage: java tlc2.tool.FPSet [-option] metadir");
//    }

}
