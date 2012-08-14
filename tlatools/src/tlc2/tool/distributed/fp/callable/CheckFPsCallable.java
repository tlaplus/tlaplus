// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.distributed.fp.callable;

import java.io.IOException;
import java.util.concurrent.Callable;
import java.util.concurrent.CountDownLatch;

import tlc2.tool.distributed.fp.FPSetRMI;

public class CheckFPsCallable implements Callable<Double> {
	private final FPSetRMI fpSetRMI;
	private final CountDownLatch cdl;
	
	public CheckFPsCallable(CountDownLatch cdl, FPSetRMI fpSetRMI) {
		this.cdl = cdl;
		this.fpSetRMI = fpSetRMI;
	}

	/* (non-Javadoc)
	 * @see java.util.concurrent.Callable#call()
	 */
	public Double call() throws Exception {
		try {
			return fpSetRMI.checkFPs();
		} catch (IOException e) {
			// not expected to happen.
			e.printStackTrace();
			// return max value to indicate to caller that the result is
			// incorrect.
			return Double.MAX_VALUE;
		} finally {
			cdl.countDown();
		}
	}
}