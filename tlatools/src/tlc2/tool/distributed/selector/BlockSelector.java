package tlc2.tool.distributed.selector;

import tlc2.tool.TLCState;
import tlc2.tool.distributed.TLCServer;
import tlc2.tool.distributed.TLCWorker;
import tlc2.tool.distributed.TLCWorkerRMI;
import tlc2.tool.queue.IStateQueue;
import tlc2.tool.queue.StateQueue;
import util.Assert;

public class BlockSelector implements IBlockSelector {
	/**
	 * A (lossy!) average block size statistic. Better not use for anything else than statistics! 
	 */
	protected volatile long averageBlockCnt = 0L;
	/**
	 * A reference to {@link TLCServer} for which this {@link IBlockSelector} selects blocks
	 */
	protected final TLCServer tlcServer;

	/**
	 * Functor pattern used to make the block size configurable that gets assigned to workers
	 * @param aTLCServer
	 */
	BlockSelector(final TLCServer aTLCServer) {
	    // LL modified error message on 7 April 2012
		Assert.check(aTLCServer != null, "TLC found a null TLCServer");
		tlcServer = aTLCServer;
	}
	
	/**
	 * Calculates the number of states a worker should be assigned. This
	 * calculation is based on the current number of workers registered with the
	 * server assigning each worker 1/N of the {@link StateQueue} with N being the
	 * current amount of {@link TLCWorker}.
	 * 
	 * The block size essentially load balances the workers by deciding how much
	 * work they get assigned.
	 * 
	 * @param stateQueue Current queue of new states
	 * @param worker {@link TLCWorker} requesting work units ({@link TLCState})
	 * @return The states that will be assigned to the given remote {@link TLCWorker} or null if no work is available
	 */
	public TLCState[] getBlocks(final IStateQueue stateQueue, final TLCWorkerRMI worker) {
		// current size of new states
		final long amountOfStates = stateQueue.size();
		// the amount of blocks that will be assigned to the work
		long blockSize = getBlockSize(amountOfStates, worker);
		// At least request a single state to guarantee StateQueue#isAvail() will be triggered
		// do not request more than what is available 
		blockSize = Math.min(blockSize, amountOfStates);
		// make sure it is positive > 0
		blockSize = Math.max(blockSize, 1);
		// can only read Integer.MAX_VALUE at max
		blockSize = Math.min(Integer.MAX_VALUE, blockSize);
		// synchronized removal from the state queue
		final TLCState[] sDequeue = stateQueue.sDequeue((int)blockSize);
		// maintain statistics with what we really got from the state queue.
		setAverageBlockCnt(sDequeue != null ? sDequeue.length : 0);
		return sDequeue;
	}

	/**
	 * @param size
	 *            The current size of the state queue.
	 * @return The intended block size.
	 */
	protected long getBlockSize(long size, final TLCWorkerRMI aWorker) {
		final int workerCount = tlcServer.getWorkerCount();
		return (long) Math.ceil(size * (1.0 / workerCount));
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.selector.IBlockSelector#setMaxTXSize(int)
	 */
	public void setMaxTXSize(int aMaximum) {
		// nop
	}
	
	protected void setAverageBlockCnt(long blockCnt) {
		// Get meaningful results right from the start
		if (averageBlockCnt > 0L) {
			averageBlockCnt = (blockCnt + averageBlockCnt) / 2L;
		} else {
			averageBlockCnt = blockCnt;
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.selector.IBlockSelector#getAverageBlockCnt()
	 */
	public long getAverageBlockCnt() {
		return averageBlockCnt;
	}
}
