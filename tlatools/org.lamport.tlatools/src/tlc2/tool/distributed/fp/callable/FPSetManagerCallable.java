// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.distributed.fp.callable;

import java.util.List;
import java.util.concurrent.Callable;

import tlc2.tool.distributed.fp.FPSetManager;
import tlc2.tool.distributed.fp.FPSetManager.FPSets;
import tlc2.util.BitVector;
import tlc2.util.LongVec;
import util.ToolIO;

public abstract class FPSetManagerCallable implements Callable<BitVectorWrapper> {
	
	protected final FPSetManager fpSetManager;
	protected final List<FPSets> fpset;
	protected final LongVec[] fps;
	protected final int index;
	
	public FPSetManagerCallable(FPSetManager fpSetManager, List<FPSets> fpSets, LongVec[] fps, int index) {
		this.fpSetManager = fpSetManager;
		this.fpset = fpSets;
		this.fps = fps;
		this.index = index;
	}
	
	protected BitVectorWrapper reassign(Exception e) throws Exception {
		ToolIO.out.println("Warning: Failed to connect from "
				+ fpSetManager.getHostName() + " to the fp server at "
				+ fpset.get(index).getHostname() + ".\n" + e.getMessage());
		if (fpSetManager.reassign(index) == -1) {
			ToolIO.out
			.println("Warning: there is no fp server available.");
			// Indicate for all fingerprints of the lost fpset that they are
			// new. This is achieved by setting all bits in BitVector.
			return new BitVectorWrapper(index, new BitVector(fps[index].size(), true));
		} else {
			// Retry with newly assigned FPSet for the given index
			return call();
		}
	}
}