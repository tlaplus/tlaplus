// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:13:19 PST by lamport
//      modified on Tue May 15 11:44:57 PDT 2001 by yuanyu

package tlc2.tool.fp;

import java.io.IOException;
import java.rmi.NoSuchObjectException;
import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;

import tlc2.tool.distributed.fp.FPSetRMI;
import tlc2.util.BitVector;
import tlc2.util.LongVec;

/**
 * An <code>FPSet</code> is a set of 64-bit fingerprints.
 *
 * Note: All concrete subclasses of this class are required to
 * guarantee that their methods are thread-safe.
 */
@SuppressWarnings("serial")
public abstract class FPSet extends UnicastRemoteObject implements FPSetRMI
{
	/**
	 * Size of a Java long in bytes
	 */
	protected static final int LongSize = 8;

	/**
	 * Counts the amount of states passed to the containsBlock method
	 */
	//TODO need AtomicLong here to prevent dirty writes to statesSeen?
	protected long statesSeen = 0L;

	protected final FPSetConfiguration fpSetConfig;
	
    protected FPSet(final FPSetConfiguration fpSetConfig) throws RemoteException {
    	this.fpSetConfig = fpSetConfig;
    }

    /**
     * Performs any initialization necessary to handle "numThreads"
     * worker threads and one main thread. Subclasses will need to
     * override this method as necessary. This method must be called
     * after the constructor but before any of the other methods below.
     */
    public abstract void init(int numThreads, String metadir, String filename) throws IOException;

    /* Returns the number of fingerprints in this set. */
    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#size()
     */
    public abstract long size();

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#put(long)
     */
    public abstract boolean put(long fp) throws IOException;

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#contains(long)
     */
    public abstract boolean contains(long fp) throws IOException;

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#close()
     */
    public void close()
    { /*SKIP*/
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#addThread()
     */
    public void addThread() throws IOException
    { /*SKIP*/
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#exit(boolean)
     */
    public abstract void exit(boolean cleanup) throws IOException;

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#checkFPs()
     */
    public abstract double checkFPs() throws IOException;

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#beginChkpt()
     */
    public abstract void beginChkpt() throws IOException;

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#commitChkpt()
     */
    public abstract void commitChkpt() throws IOException;

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#recover()
     */
    public abstract void recover() throws IOException;

    public abstract void recoverFP(long fp) throws IOException;

    public abstract void prepareRecovery() throws IOException;

    public abstract void completeRecovery() throws IOException;

    /* The set of checkpoint methods for remote checkpointing. */
    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#beginChkpt(java.lang.String)
     */
    public abstract void beginChkpt(String filename) throws IOException;

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#commitChkpt(java.lang.String)
     */
    public abstract void commitChkpt(String filename) throws IOException;

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#recover(java.lang.String)
     */
    public abstract void recover(String filename) throws IOException;
    
	/**
	 * @return true iff no invaritant is violated.
	 * @throws IOException
	 */
	public boolean checkInvariant() throws IOException {
		return true;
	}
	
	/**
	 * @param expectFPs
	 *            The expected amount of fingerprints stored in this
	 *            {@link FPSet}
	 * @return true iff no invaritant is violated and the FPSet contains the
	 *         expected amount of fingerprints.
	 * @throws IOException
	 */
	public boolean checkInvariant(long expectFPs) throws IOException {
		return true;
	}

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#putBlock(tlc2.util.LongVec)
     */
    public BitVector putBlock(LongVec fpv) throws IOException
    {
        int size = fpv.size();
		BitVector bv = new BitVector(size);
        for (int i = 0; i < fpv.size(); i++)
        {
			// TODO Figure out why corresponding value in BitVector is inverted
			// compared to put(long)
            if (!this.put(fpv.elementAt(i)))
            {
                bv.set(i);
            }
        }
        return bv;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#containsBlock(tlc2.util.LongVec)
     */
    public BitVector containsBlock(LongVec fpv) throws IOException
    {
    	statesSeen += fpv.size();
        BitVector bv = new BitVector(fpv.size());
        for (int i = 0; i < fpv.size(); i++)
        {
			// TODO Figure out why corresponding value in BitVector is inverted
			// compared to contains(long)
            if (!this.contains(fpv.elementAt(i)))
            {
                bv.set(i);
            }
        }
        return bv;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetRMI#getStatesSeen()
     */
    public long getStatesSeen() throws RemoteException {
    	return statesSeen;
    }
    
    public FPSetConfiguration getConfiguration() {
    	return fpSetConfig;
    }

	/**
	 * @param fpBits
	 * @return
	 */
	public static boolean isValid(int fpBits) {
		return fpBits >= 0 && fpBits <= MultiFPSet.MAX_FPBITS;
	}

	/**
	 * @see UnicastRemoteObject#unexportObject(java.rmi.Remote, boolean)
	 * @param force
	 * @throws NoSuchObjectException
	 */
	public void unexportObject(boolean force) throws NoSuchObjectException {
		UnicastRemoteObject.unexportObject(this, force);
	}
}
