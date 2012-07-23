// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.distributed;

import java.io.IOException;

import tlc2.tool.fp.FPSet;
import tlc2.util.BitVector;
import tlc2.util.LongVec;

public interface IFPSetManager {

	public abstract int numOfServers();

	/**
	 * @see FPSet#close()
	 */
	public abstract void close(boolean cleanup) throws IOException;

	/**
	 * @see FPSet#put(long)
	 */
	public abstract boolean put(long fp);

	/**
	 * @see FPSet#putBlock(LongVec)
	 */
	public abstract BitVector[] putBlock(LongVec[] fps);

	/**
	 * @see FPSet#containsBlock(LongVec);
	 */
	public abstract BitVector[] containsBlock(LongVec[] fps);

	/**
	 * @see FPSet#size()
	 */
	public abstract long size();

	/**
	 * @return The amount of states seen by all {@link FPSet}. This amounts to
	 *         the states computed by all {@link TLCWorker}
	 */
	public abstract long getStatesSeen();

	public abstract void checkpoint(String fname) throws InterruptedException;

	public abstract void recover(String fname) throws InterruptedException;

}