// Copyright (c) 2016 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.distributed.fp.callable;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.distributed.fp.FPSetRMI;

import java.io.IOException;
import java.util.concurrent.Callable;

public class CheckInvariantCallable implements Callable<Boolean> {
    private final FPSetRMI fpSetRMI;

    public CheckInvariantCallable(final FPSetRMI fpSetRMI) {
        this.fpSetRMI = fpSetRMI;
    }

    /* (non-Javadoc)
     * @see java.util.concurrent.Callable#call()
     */
    @Override
    public Boolean call() {
        try {
            return fpSetRMI.checkInvariant();
        } catch (final IOException e) {
            // not expected to happen.
            MP.printError(EC.GENERAL, e);
            // return max value to indicate to caller that the result is
            // incorrect.
            return false;
        }
    }
}