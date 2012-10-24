// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.distributed.fp.callable;

import java.io.IOException;
import java.util.concurrent.Callable;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.distributed.fp.FPSetRMI;

public class CheckFPsCallable implements Callable<Double> {
	private final FPSetRMI fpSetRMI;
	
	public CheckFPsCallable(FPSetRMI fpSetRMI) {
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
			MP.printError(EC.GENERAL, e);
			// return max value to indicate to caller that the result is
			// incorrect.
			return Double.MAX_VALUE;
		}
	}
}