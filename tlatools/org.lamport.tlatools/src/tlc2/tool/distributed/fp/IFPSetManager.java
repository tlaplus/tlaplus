// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.distributed.fp;

import java.io.IOException;
import java.io.Serializable;
import java.util.concurrent.ExecutorService;

import tlc2.tool.distributed.fp.FPSetManager.FPSets;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.fp.MSBDiskFPSet;
import tlc2.util.BitVector;
import tlc2.util.LongVec;

/**
 *
 */
public interface IFPSetManager extends Serializable {

	/**
	 * @see FPSetRMI#checkFPs()
	 */
	long checkFPs();

	/**
	 * @see FPSetRMI#checkInvariant()
	 */
	boolean checkInvariant();
	
	/**
	 */
	void checkpoint(String fname) throws InterruptedException, IOException;

	/**
	 * @see FPSetRMI#close()
	 */
	void close(boolean cleanup) throws IOException;

	/**
	 * @see FPSetRMI#commitChkpt()
	 */
	void commitChkpt() throws IOException;

	/**
	 * @see FPSetRMI#contains(long)
	 */
	boolean contains(long fp);

	/**
	 * The given {@link LongVec} has to have the same size as
	 * {@link IFPSetManager#numOfServers()}.
	 * <p>
	 * As a second pre-condition, the fingerprints in the {@link LongVec} have
	 * to be ordered corresponding with the fingerprint space partitioning used
	 * by this {@link IFPSetManager}. It is the callers responsibility to set up
	 * the {@link LongVec} in this way (for efficiency reasons).
	 * 
	 * @see IFPSetManager#numOfServers()
	 * @see IFPSetManager#getFPSetIndex(long)
	 * @see FPSetRMI#containsBlock(LongVec)
	 */
	BitVector[] containsBlock(LongVec[] fps);

	/**
	 * The given {@link LongVec} has to have the same size as
	 * {@link IFPSetManager#numOfServers()}.
	 * 
	 * @see FPSetRMI#containsBlock(LongVec);
	 */
	BitVector[] containsBlock(LongVec[] fps, ExecutorService executorService);

	/**
	 * The index of the {@link FPSetRMI} corresponding with the given
	 * fingerprint in this {@link IFPSetManager}. It is used by worker nodes to
	 * pre-sort the fingerprints in {@link LongVec} according to the index of
	 * the {@link FPSetRMI} responsible for the subset of the fingerprint space.
	 * 
	 * @param fp
	 *            The fingerprint for which the index should be calculated.
	 * @return The index of the {@link FPSet} that is assigned this subset of
	 *         the fingerprint space.
	 *         <p>
	 *         Assignment is based on the least significant bits. This selection
	 *         of fingerprint bits is important. Selecting the most significant
	 *         bits of a fingerprint to assign an {@link FPSet} would violate
	 *         the invariant of MSB-based {@link FPSet}s such as
	 *         {@link MSBDiskFPSet}. They assume that the
	 *         {@link FPSetConfiguration#getFpBits()} are fixed. FPSetManager
	 *         may dynamically reassign additional subsets of the fingerprint
	 *         space to an existing {@link FPSet}, when the previously assigned
	 *         {@link FPSet} is lost due to a network or hardware failure.
	 */
	int getFPSetIndex(final long fp);

	/**
	 * @see FPSetRMI#getStatesSeen()
	 */
	long getStatesSeen();

	/**
	 * @return The number of {@link FPSetRMI} instances backing this
	 *         {@link IFPSetManager}.
	 *         <p>
	 *         The {@link IFPSetManager} distributes the fingerprint space
	 *         across the number of instances at its own discretion.
	 */
	int numOfServers();

	/**
	 * @return The number of alive {@link FPSetRMI} instances backing this
	 *         {@link IFPSetManager}. It results a value in the range [0,
	 *         {@link IFPSetManager#numOfServers()}]<p>
	 *         It does <b>not</b> re-count reassigned {@link FPSets}. 
	 * 
	 * @see IFPSetManager#numOfServers()
	 */
	int numOfAliveServers();

	/**
	 * @see FPSetRMI#put(long)
	 */
	boolean put(long fp);

	/**
	 * The given {@link LongVec} has to have the same size as
	 * {@link IFPSetManager#numOfServers()}.
	 * 
	 * @see FPSetRMI#putBlock(LongVec)
	 */
	BitVector[] putBlock(LongVec[] fps);

	/**
	 * The given {@link LongVec} has to have the same size as
	 * {@link IFPSetManager#numOfServers()}.
	 * 
	 * @see FPSetRMI#putBlock(LongVec)
	 */
	BitVector[] putBlock(LongVec[] fps, ExecutorService executorService);

	/**
	 * @see FPSetRMI#recover(String)
	 */
	void recover(String fname) throws InterruptedException, IOException;

	/**
	 * Registers the given {@link FPSetRMI} as a usable instance of this
	 * {@link IFPSetManager}. This means that the given {@link FPSetRMI} will be
	 * used to store and lookup fingerprints during model checking. It is up to
	 * the {@link IFPSetManager} to partition the fingerprint space, meaning the
	 * {@link FPSetRMI} will not see all fingerprints of all distinct states.
	 */
	void register(FPSetRMI fpSet, String hostname) throws FPSetManagerException;

	/**
	 * @see FPSetRMI#size()
	 */
	long size();
}