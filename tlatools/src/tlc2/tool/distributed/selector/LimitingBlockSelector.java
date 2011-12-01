package tlc2.tool.distributed.selector;

import tlc2.tool.distributed.TLCServer;
import tlc2.tool.distributed.TLCWorkerRMI;

public class LimitingBlockSelector extends BlockSelector {

	private int maximum;

	/**
	 * Limits the block size to 8192
	 * @param aTLCServer
	 */
	LimitingBlockSelector(final TLCServer aTLCServer) {
		this(aTLCServer, 8192);
	}
	
	LimitingBlockSelector(final TLCServer aTLCServer, final int aMaximum) {
		super(aTLCServer);
		this.maximum = aMaximum;
	}

	/**
	 * Limits the block size to a defined maximum if the dynamically calculated
	 * block size exceeds it
	 */
	protected long getBlockSize(final long size, final TLCWorkerRMI aWorker) {
		final long blockSize = super.getBlockSize(size, aWorker);
		if(blockSize > maximum) {
			return maximum;
		}
		return blockSize;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.selector.IBlockSelector#setMaxTXSize(int)
	 */
	public void setMaxTXSize(int aMaximum) {
		maximum = aMaximum;
	}
	
	protected int getMaximum() {
		return maximum;
	}
}
