package tlc2.tool.distributed.selector;

import tlc2.output.EC;
import tlc2.tool.TLCState;
import tlc2.tool.distributed.TLCServer;
import tlc2.tool.distributed.TLCWorker;
import tlc2.tool.distributed.TLCWorkerRMI;
import tlc2.tool.queue.StateQueue;
import util.Assert;

public class BlockSelector implements IBlockSelector {
	/**
	 * A reference to {@link TLCServer} for which this {@link IBlockSelector} selects blocks
	 */
	protected final TLCServer tlcServer;

	/**
	 * Functor pattern used to make the block size configurable that gets assigned to workers
	 * @param aTLCServer
	 */
	BlockSelector(final TLCServer aTLCServer) {
		Assert.check(aTLCServer != null, EC.GENERAL);
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
	 * @return The states that will be assigned to the given remote {@link TLCWorker}
	 */
	public TLCState[] getBlocks(final StateQueue stateQueue, final TLCWorkerRMI worker) {
		// current size of new states
		final int amountOfStates = stateQueue.size();
		// the amount of blocks that will be assigned to the work
		final int blockSize = getBlockSize(amountOfStates);
		// synchronized removal from the state queue
		return stateQueue.sDequeue(blockSize);
	}

	/**
	 * @param size
	 *            The current size of the state queue.
	 * @return The intended block size
	 */
	protected int getBlockSize(int size) {
		return (int) Math.ceil(size * (1.0 / tlcServer.getWorkerCount()));
	}
}
