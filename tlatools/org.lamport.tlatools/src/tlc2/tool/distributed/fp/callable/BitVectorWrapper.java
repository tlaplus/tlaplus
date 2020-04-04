// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.distributed.fp.callable;

import tlc2.util.BitVector;

public class BitVectorWrapper {
	
	private final int index;
	private final BitVector bitVector;
	
	public BitVectorWrapper(final int index, final BitVector bv) {
		this.index = index;
		this.bitVector = bv;
	}

	/**
	 * @return the bitVector
	 */
	public BitVector getBitVector() {
		return bitVector;
	}

	/**
	 * @return the index
	 */
	public int getIndex() {
		return index;
	}
}
