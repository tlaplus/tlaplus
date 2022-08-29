// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:13:35 PST by lamport
//      modified on Fri Dec 15 15:24:57 PST 2000 by yuanyu
package tlc2.tool.distributed.fp;

import tlc2.tool.TLCTrace;
import tlc2.tool.fp.FPSet;
import tlc2.util.LongVec;

import java.io.IOException;
import java.rmi.Remote;
import java.rmi.RemoteException;
import java.util.BitSet;

/**
 * @author Simon Zambrovski
 */

/**
 * @author markus
 */
public interface FPSetRMI extends Remote, AutoCloseable {

    void addThread() throws IOException;

    void beginChkpt() throws IOException;

    void beginChkpt(String filename) throws IOException;

    /**
     * @return The minimum distance of all fingerprints in this {@link FPSet}.
     * This distance reflects the probability of a fingerprint
     * collision.
     */
    long checkFPs() throws IOException;

    /**
     * @see FPSet#checkInvariant()
     */
    boolean checkInvariant() throws IOException;

    void commitChkpt() throws IOException;

    void commitChkpt(String filename) throws IOException;

    /**
     * Returns <code>true</code> iff the fingerprint <code>fp</code> is
     * in this {@link FPSet}.
     */
    boolean contains(long fp) throws IOException;

    /**
     * Checks existence in the {@link FPSet} for each fingerprints contained in
     * the given {@link LongVec}.
     * <p>
     * Contrary to {@link FPSet#contains(long)}, bits in the resulting
     * {@link BitSet} are set if the fingerprints are _not_ in this
     * {@link FPSet}.
     *
     * @see FPSetRMI#contains(long)
     */
    BitSet containsBlock(LongVec fpv) throws IOException;

    /**
     * @return The amount of states seen by this FPSet (not distinct states!)
     */
    long getStatesSeen() throws RemoteException;

    /**
     * Returns <code>true</code> iff the fingerprint <code>fp</code> is
     * in this set. If the fingerprint is not in the set, it is added to
     * the {@link FPSet} as a side-effect.
     */
    boolean put(long fp) throws IOException;

    /**
     * Checks existence in the {@link FPSet} for each fingerprints contained in
     * the given {@link LongVec}. As a side-effect, new fingerprints are added
     * to the {@link FPSet}.
     * <p>
     * Contrary to {@link FPSet#put(long)}, bits in the resulting
     * {@link BitSet} are set if the fingerprints have _not_ been in this
     * {@link FPSet}.
     *
     * @see FPSet#put(long)
     */
    BitSet putBlock(LongVec fpv) throws IOException;

    void recover(TLCTrace trace) throws IOException;

    void recover(String filename) throws IOException;

    /**
     * @return Corresponds to the amount of distinct states seen by this
     * {@link FPSet} instance (if only a single {@link FPSet} is used
     * for model checking, this number corresponds to the distinct
     * states found overall).
     */
    long size() throws IOException;
}
