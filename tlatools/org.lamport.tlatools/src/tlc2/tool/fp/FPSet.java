// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:13:19 PST by lamport
//      modified on Tue May 15 11:44:57 PDT 2001 by yuanyu

package tlc2.tool.fp;

import tlc2.tool.distributed.fp.DistributedFPSet;
import tlc2.tool.distributed.fp.FPSetRMI;
import tlc2.util.LongVec;

import java.io.IOException;
import java.rmi.NoSuchObjectException;
import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;
import java.util.BitSet;

/**
 * An <code>FPSet</code> is a set of 64-bit fingerprints.
 * <p>
 * Note: All concrete subclasses of this class are required to
 * guarantee that their methods are thread-safe.
 */
@SuppressWarnings("serial")
public abstract class FPSet extends UnicastRemoteObject implements FPSetRMI {
    /**
     * Size of a Java long in bytes
     */
    protected static final long LongSize = 8;
    protected final FPSetConfiguration fpSetConfig;
    /**
     * Counts the amount of states passed to the containsBlock method
     */
    //TODO need AtomicLong here to prevent dirty writes to statesSeen?
    protected long statesSeen = 0L;

    protected FPSet(final FPSetConfiguration fpSetConfig) throws RemoteException {
        this.fpSetConfig = fpSetConfig;
    }

    /**
     *
     */
    public static boolean isValid(final int fpBits) {
        return fpBits >= 0 && fpBits <= MultiFPSet.MAX_FPBITS;
    }

    /**
     * Performs any initialization necessary to handle "numThreads"
     * worker threads and one main thread. Subclasses will need to
     * override this method as necessary. This method must be called
     * after the constructor but before any of the other methods below.
     */
    public abstract FPSet init(int numThreads, String metadir, String filename) throws IOException;

    public void incWorkers(final int num) {
        // subclasses may override
    }

    /* Returns the number of fingerprints in this set. */
    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#size()
     */
    @Override
    public abstract long size();


    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#close()
     */
    @Override
    public void close() throws Exception {
        // If DistributedFPSet is running, signal termination and wake it up.
        // This is necessary when a SecurityManager intercepts System.exit(int)
        // calls which has the side effect that DistributedFPSet's reporting
        // loop does not terminate and keeps going forever.
        DistributedFPSet.shutdown();
        synchronized (this) {
            this.notify();
        }

        try {
            UnicastRemoteObject.unexportObject(this, true);
        } catch (NoSuchObjectException e) {
        }

    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#addThread()
     */
    @Override
    public void addThread() throws IOException { /*SKIP*/
    }

    public abstract void recoverFP(long fp) throws IOException;

    /**
     * @return true iff no invaritant is violated.
     */
    @Override
    public boolean checkInvariant() throws IOException {
        return true;
    }

    /**
     * @param expectFPs The expected amount of fingerprints stored in this
     *                  {@link FPSet}
     * @return true iff no invaritant is violated and the FPSet contains the
     * expected amount of fingerprints.
     */
    public boolean checkInvariant(final long expectFPs) throws IOException {
        return true;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#putBlock(tlc2.util.LongVec)
     */
    @Override
    public BitSet putBlock(final LongVec fpv) throws IOException {
        final int size = fpv.size();
        final BitSet bv = new BitSet(size);
        for (int i = 0; i < fpv.size(); i++) {
            // TODO Figure out why corresponding value in BitSet is inverted
            // compared to put(long)
            if (!this.put(fpv.get(i))) {
                bv.set(i);
            }
        }
        return bv;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#containsBlock(tlc2.util.LongVec)
     */
    @Override
    public BitSet containsBlock(final LongVec fpv) throws IOException {
        statesSeen += fpv.size();
        final BitSet bv = new BitSet(fpv.size());
        for (int i = 0; i < fpv.size(); i++) {
            // TODO Figure out why corresponding value in BitSet is inverted
            // compared to contains(long)
            if (!this.contains(fpv.get(i))) {
                bv.set(i);
            }
        }
        return bv;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#getStatesSeen()
     */
    @Override
    public long getStatesSeen() throws RemoteException {
        return statesSeen;
    }

    public FPSetConfiguration getConfiguration() {
        return fpSetConfig;
    }

    /**
     * @see UnicastRemoteObject#unexportObject(java.rmi.Remote, boolean)
     */
    public void unexportObject(final boolean force) throws NoSuchObjectException {
        UnicastRemoteObject.unexportObject(this, force);
    }
}
