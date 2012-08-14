// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.distributed.fp.callable;

import java.util.concurrent.Callable;
import java.util.concurrent.CountDownLatch;

import tlc2.tool.distributed.fp.FPSetManager;
import tlc2.tool.distributed.fp.FPSetManager.FPSets;
import tlc2.util.BitVector;
import tlc2.util.LongVec;

public abstract class FPSetManagerCallable implements Callable<BitVector> {
	
	protected final FPSetManager fpSetManager;
	protected final FPSets fpset;
	protected final LongVec[] fps;
	protected final int index;
	protected final CountDownLatch cdl;
	
	public FPSetManagerCallable(FPSetManager fpSetManager, CountDownLatch cdl, FPSets fpset, LongVec[] fps, int index) {
		this.fpSetManager = fpSetManager;
		this.cdl = cdl;
		this.fpset = fpset;
		this.fps = fps;
		this.index = index;
	}
	
	//TODO Does this behave correctly if multiple threads execute it concurrently?
	protected BitVector reassign(Exception e) {
		System.out.println("Warning: Failed to connect from "
				+ fpSetManager.getHostName() + " to the fp server at "
				+ fpset.getHostname() + ".\n" + e.getMessage());
		if (fpSetManager.reassign(index) == -1) {
			System.out
			.println("Warning: there is no fp server available.");
		}
		BitVector bitVector = new BitVector(fps[index].size());
		bitVector.set(0, fps[index].size() - 1);
		return bitVector;
	}
}