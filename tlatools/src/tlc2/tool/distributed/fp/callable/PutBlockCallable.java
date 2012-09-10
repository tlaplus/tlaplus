// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.distributed.fp.callable;

import java.util.List;

import tlc2.tool.distributed.fp.FPSetManager;
import tlc2.tool.distributed.fp.FPSetManager.FPSets;
import tlc2.util.BitVector;
import tlc2.util.LongVec;

public class PutBlockCallable extends FPSetManagerCallable {
	
	public PutBlockCallable(FPSetManager fpSetManager, List<FPSets> fpSets, LongVec[] fps, int index) {
		super(fpSetManager, fpSets, fps, index);
	}
	
	/* (non-Javadoc)
	 * @see java.util.concurrent.Callable#call()
	 */
	public BitVector call() throws Exception {
		try {
			return fpset.get(index).putBlock(fps[index]);
		} catch (Exception e) {
			return reassign(e);
		}
	}
}