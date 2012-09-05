// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.distributed.fp;

import java.io.IOException;
import java.io.Serializable;
import java.util.concurrent.ExecutorService;

import tlc2.tool.distributed.TLCWorker;
import tlc2.tool.fp.FPSet;
import tlc2.util.BitVector;
import tlc2.util.LongVec;

public interface IFPSetManager extends Serializable {

	int numOfServers();

	/**
	 * @see FPSet#close()
	 */
	void close(boolean cleanup) throws IOException;

	/**
	 * @see FPSet#put(long)
	 */
	boolean put(long fp);

	/**
	 * @see FPSet#contains(long)
	 */
	boolean contains(long fp);
	
	/**
	 * @see FPSet#putBlock(LongVec)
	 */
	BitVector[] putBlock(LongVec[] fps);

	/**
	 * @see FPSet#containsBlock(LongVec);
	 */
	BitVector[] containsBlock(LongVec[] fps);

	/**
	 * @see FPSet#putBlock(LongVec)
	 */
	BitVector[] putBlock(LongVec[] fps, ExecutorService executorService);
	
	/**
	 * @see FPSet#containsBlock(LongVec);
	 */
	BitVector[] containsBlock(LongVec[] fps, ExecutorService executorService);

	/**
	 * @see FPSet#size()
	 */
	long size();

	/**
	 * @return The amount of states seen by all {@link FPSet}. This amounts to
	 *         the states computed by all {@link TLCWorker}
	 */
	long getStatesSeen();

	void checkpoint(String fname) throws InterruptedException, IOException;

	void recover(String fname) throws InterruptedException, IOException;

	void register(FPSetRMI fpSet, String hostname) throws FPSetManagerException;

	long getMask();

	double checkFPs();

	void addThread() throws IOException;

	void commitChkpt() throws IOException;

}