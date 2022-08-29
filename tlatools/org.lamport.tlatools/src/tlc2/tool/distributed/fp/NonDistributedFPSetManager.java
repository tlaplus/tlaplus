// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.distributed.fp;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.TLCTrace;
import tlc2.util.LongVec;

import java.io.IOException;
import java.util.BitSet;
import java.util.concurrent.ExecutorService;

@SuppressWarnings("serial")
public class NonDistributedFPSetManager implements IFPSetManager {

    private final FPSetRMI fpSet;
    private final String hostname;
    private final transient TLCTrace trace; // Do not serialize trace and send it over the wire. Recovery executes on the master, not on the workers.

    public NonDistributedFPSetManager(final FPSetRMI fpSet,
                                      final String hostname, final TLCTrace trace) {
        this.fpSet = fpSet;
        this.hostname = hostname;
        this.trace = trace;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.IFPSetManager#register(tlc2.tool.distributed.fp.FPSetRMI, java.lang.String)
     */
    @Override
    public void register(final FPSetRMI fpSet, final String hostname) {
        throw new UnsupportedOperationException("Not applicable for non-distributed FPSetManager");
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetManager#numOfServers()
     */
    @Override
    public int numOfServers() {
        return 1;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.IFPSetManager#numOfAliveServers()
     */
    @Override
    public int numOfAliveServers() {
        return numOfServers();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetManager#getHostName()
     */
    public String getHostName() {
        return hostname;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetManager#put(long)
     */
    @Override
    public boolean put(final long fp) {
        try {
            return this.fpSet.put(fp);
        } catch (final IOException e) {
            // not expected to happen
            MP.printError(EC.GENERAL, e);
            return false;
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetManager#contains(long)
     */
    @Override
    public boolean contains(final long fp) {
        try {
            return this.fpSet.contains(fp);
        } catch (final IOException e) {
            // not expected to happen
            MP.printError(EC.GENERAL, e);
            return false;
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.IFPSetManager#getFPSetIndex(long)
     */
    @Override
    public int getFPSetIndex(final long fp) {
        return 0;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetManager#putBlock(tlc2.util.LongVec[])
     */
    @Override
    public BitSet[] putBlock(final LongVec[] fps) {
        final BitSet[] res = new BitSet[fps.length];
        for (int i = 0; i < fps.length; i++) {
            final LongVec longVec = fps[i];
            try {
                res[i] = this.fpSet.putBlock(longVec);
            } catch (final IOException e) {
                // not expected to happen
                MP.printError(EC.GENERAL, e);
                res[i] = new BitSet(0);
            }
        }
        return res;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetManager#putBlock(tlc2.util.LongVec[], java.util.concurrent.ExecutorService)
     */
    @Override
    public BitSet[] putBlock(final LongVec[] fps, final ExecutorService executorService) {
        return putBlock(fps);
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetManager#containsBlock(tlc2.util.LongVec[])
     */
    @Override
    public BitSet[] containsBlock(final LongVec[] fps) {
        final BitSet[] res = new BitSet[fps.length];
        for (int i = 0; i < fps.length; i++) {
            final LongVec longVec = fps[i];
            try {
                res[i] = this.fpSet.containsBlock(longVec);
            } catch (final IOException e) {
                // not expected to happen
                MP.printError(EC.GENERAL, e);
                res[i] = new BitSet(0);
            }
        }
        return res;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetManager#containsBlock(tlc2.util.LongVec[], java.util.concurrent.ExecutorService)
     */
    @Override
    public BitSet[] containsBlock(final LongVec[] fps,
                                  final ExecutorService executorService) {
        return containsBlock(fps);
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetManager#checkFPs()
     */
    @Override
    public long checkFPs() {
        try {
            return this.fpSet.checkFPs();
        } catch (final IOException e) {
            // not expected to happen
            MP.printError(EC.GENERAL, e);
            return -1;
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.IFPSetManager#checkInvariant()
     */
    @Override
    public boolean checkInvariant() {
        try {
            return this.fpSet.checkInvariant();
        } catch (final IOException e) {
            // not expected to happen
            MP.printError(EC.GENERAL, e);
            return false;
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetManager#size()
     */
    @Override
    public long size() {
        try {
            return this.fpSet.size();
        } catch (final IOException e) {
            // not supposed to happen
            MP.printError(EC.GENERAL, e);
            return -1;
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetManager#getStatesSeen()
     */
    @Override
    public long getStatesSeen() {
        try {
            return this.fpSet.size();
        } catch (final IOException e) {
            // not supposed to happen
            MP.printError(EC.GENERAL, e);
            return -1;
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetManager#getMask()
     */
    public long getMask() {
        return Long.MAX_VALUE;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetManager#checkpoint(java.lang.String)
     */
    @Override
    public void checkpoint(final String fname) throws IOException {
        this.fpSet.beginChkpt();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.IFPSetManager#commitChkpt()
     */
    @Override
    public void commitChkpt() throws IOException {
        this.fpSet.commitChkpt();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetManager#recover(java.lang.String)
     */
    @Override
    public void recover(final String fname) throws IOException {
        this.fpSet.recover(trace);
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.fp.FPSetManager#close(boolean)
     */
    @Override
    public void close() throws Exception {
        this.fpSet.close();
    }
}
