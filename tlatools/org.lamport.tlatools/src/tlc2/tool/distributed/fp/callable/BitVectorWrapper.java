// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.distributed.fp.callable;

import java.util.BitSet;

public class BitVectorWrapper {

    private final int index;
    private final BitSet bitVector;

    public BitVectorWrapper(final int index, final BitSet bv) {
        this.index = index;
        this.bitVector = bv;
    }

    /**
     * @return the bitVector
     */
    public BitSet getBitVector() {
        return bitVector;
    }

    /**
     * @return the index
     */
    public int getIndex() {
        return index;
    }
}
