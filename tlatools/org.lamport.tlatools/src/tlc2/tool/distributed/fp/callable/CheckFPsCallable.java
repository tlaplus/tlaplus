// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.distributed.fp.callable;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.distributed.fp.FPSetRMI;

import java.io.IOException;
import java.util.concurrent.Callable;

public class CheckFPsCallable implements Callable<Long> {
    private final FPSetRMI fpSetRMI;

    public CheckFPsCallable(final FPSetRMI fpSetRMI) {
        this.fpSetRMI = fpSetRMI;
    }

    /* (non-Javadoc)
     * @see java.util.concurrent.Callable#call()
     */
    @Override
    public Long call() {
        try {
            return fpSetRMI.checkFPs();
        } catch (final IOException e) {
            // not expected to happen.
            MP.printError(EC.GENERAL, e);
            // return max value to indicate to caller that the result is
            // incorrect.
            return Long.MAX_VALUE;
        }
    }
}