// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.distributed.fp.callable;

import tlc2.tool.distributed.fp.FPSetManager;
import tlc2.tool.distributed.fp.FPSetManager.FPSets;
import tlc2.util.LongVec;
import util.ToolIO;

import java.util.BitSet;
import java.util.List;
import java.util.concurrent.Callable;

public abstract class FPSetManagerCallable implements Callable<BitVectorWrapper> {

    protected final FPSetManager fpSetManager;
    protected final List<FPSets> fpset;
    protected final LongVec[] fps;
    protected final int index;

    public FPSetManagerCallable(final FPSetManager fpSetManager, final List<FPSets> fpSets, final LongVec[] fps, final int index) {
        this.fpSetManager = fpSetManager;
        this.fpset = fpSets;
        this.fps = fps;
        this.index = index;
    }

    protected BitVectorWrapper reassign(final Exception e) throws Exception {
        ToolIO.out.println("Warning: Failed to connect from "
                + fpSetManager.getHostName() + " to the fp server at "
                + fpset.get(index).getHostname() + ".\n" + e.getMessage());
        if (fpSetManager.reassign(index) == -1) {
            ToolIO.out
                    .println("Warning: there is no fp server available.");
            // Indicate for all fingerprints of the lost fpset that they are
            // new. This is achieved by setting all bits in BitSet.
            final var size = fps[index].size();
            final var bitSet = new BitSet(size);
            bitSet.set(0, size, true);
            return new BitVectorWrapper(index, bitSet);
        } else {
            // Retry with newly assigned FPSet for the given index
            return call();
        }
    }
}