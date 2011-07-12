package tlc2.tool.distributed.selector;

import tlc2.tool.distributed.TLCServer;

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
	protected int getBlockSize(int size) {
		final int blockSize = super.getBlockSize(size);
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
}
