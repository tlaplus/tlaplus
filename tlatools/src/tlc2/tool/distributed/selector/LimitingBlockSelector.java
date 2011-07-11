package tlc2.tool.distributed.selector;

import tlc2.tool.distributed.TLCServer;

public class LimitingBlockSelector extends BlockSelector {

	private final int maximum;

	/**
	 * Limits the block size to 1024
	 * @param aTLCServer
	 */
	LimitingBlockSelector(final TLCServer aTLCServer) {
		this(aTLCServer, 1024);
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
		int blockSize = super.getBlockSize(size);
		if(blockSize > maximum) {
			return maximum;
		}
		return blockSize;
	}
}
