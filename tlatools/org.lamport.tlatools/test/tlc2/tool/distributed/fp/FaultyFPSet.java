// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.distributed.fp;

import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.fp.MemFPSet;

import java.rmi.RemoteException;

@SuppressWarnings("serial")
public class FaultyFPSet extends MemFPSet implements FPSetRMI {

    private int putInvocations = 0;
    private int containsInvocations = 0;

    protected FaultyFPSet() throws RemoteException {
        super(new FPSetConfiguration());
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.MemFPSet#put(long)
     */
    @Override
    public synchronized boolean put(final long fp) {
        // Simulate network error after a single successful invocation
        if (putInvocations++ > 0) {
            throw new RuntimeException("Test FPSet");
        }
        return super.put(fp);
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.MemFPSet#contains(long)
     */
    @Override
    public synchronized boolean contains(final long fp) {
        // Simulate network error after a single successful invocation
        if (containsInvocations++ > 0) {
            throw new RuntimeException("Test FPSet");
        }
        return super.contains(fp);
    }
}
