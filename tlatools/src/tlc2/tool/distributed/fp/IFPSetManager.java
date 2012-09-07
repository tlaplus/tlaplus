// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.distributed.fp;

import java.io.IOException;
import java.io.Serializable;
import java.util.concurrent.ExecutorService;

import tlc2.util.BitVector;
import tlc2.util.LongVec;

public interface IFPSetManager extends Serializable {

	/**
	 * @see FPSetRMI#addThread()
	 */
	void addThread() throws IOException;

	/**
	 * @see FPSetRMI#checkFPs()
	 */
	double checkFPs();

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
	 * @see FPSetRMI#containsBlock(LongVec);
	 */
	BitVector[] containsBlock(LongVec[] fps);
	
	/**
	 * @see FPSetRMI#containsBlock(LongVec);
	 */
	BitVector[] containsBlock(LongVec[] fps, ExecutorService executorService);

	/**
	 * The index address of the {@link FPSetRMI} corresponding with the given
	 * fingerprint in this {@link IFPSetManager}. It is used by worker nodes to
	 * pre-sort the fingerprints in {@link LongVec} according to the index of
	 * the {@link FPSetRMI} responsible for the partition of the fingerprint
	 * space.
	 */
	int getFPSetIndex(long fp);

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
	 * @see FPSetRMI#put(long)
	 */
	boolean put(long fp);

	/**
	 * @see FPSetRMI#putBlock(LongVec)
	 */
	BitVector[] putBlock(LongVec[] fps);

	/**
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