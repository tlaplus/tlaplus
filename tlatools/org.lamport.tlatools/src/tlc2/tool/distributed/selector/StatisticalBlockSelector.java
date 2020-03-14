package tlc2.tool.distributed.selector;

import tlc2.tool.distributed.TLCServer;
import tlc2.tool.distributed.TLCWorkerRMI;
import tlc2.tool.distributed.TLCWorkerSmartProxy;

public class StatisticalBlockSelector extends LimitingBlockSelector {

	/**
	 * Maximum total network overhead we are willing to take
	 */
	private final double networkOverheadLimit;

	/**
	 * @param aTLCServer
	 */
	public StatisticalBlockSelector(final TLCServer aTLCServer) {
		super(aTLCServer);
		this.networkOverheadLimit = 2.5 / 100d; 
	}

	/**
	 * @param size
	 *            The current size of the state queue.
	 * @return The intended block size
	 */
	protected long getBlockSize(final long size, final TLCWorkerRMI aWorker) {
		// has to be correct type and statistics have to be available
		if(aWorker instanceof TLCWorkerSmartProxy) {
			final TLCWorkerSmartProxy proxy = (TLCWorkerSmartProxy) aWorker;
			int blockSize = (int) Math.min(Math.max(
					Math.abs(Math.ceil(size * (proxy.getNetworkOverhead() / networkOverheadLimit))), 1), getMaximum());
			return blockSize;
		}
		
		// default return value
		return super.getBlockSize(size, aWorker);
	}
}
