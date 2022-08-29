// Copyright (c) Jan 4, 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.distributed.management;

import tlc2.TLCGlobals;
import tlc2.tool.TLCState;
import tlc2.tool.distributed.TLCServer;
import tlc2.tool.distributed.fp.IFPSetManager;
import tlc2.tool.management.TLCStandardMBean;

import javax.management.NotCompliantMBeanException;
import java.io.IOException;
import java.rmi.RemoteException;

/**
 * @author Markus Alexander Kuppe
 */
public class TLCServerMXWrapper extends TLCStandardMBean implements TLCStatisticsMXBean {

    private final TLCServer tlcServer;

    public TLCServerMXWrapper(final TLCServer aTLCServer)
            throws NotCompliantMBeanException {
        super(TLCStatisticsMXBean.class);
        tlcServer = aTLCServer;

        // register all TLCStatisticsMXBeans under the same name
        registerMBean("tlc2.tool:type=ModelChecker");
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getStatesGenerated()
     */
    @Override
    public long getStatesGenerated() {
        if (tlcServer.isRunning()) {
            return tlcServer.getStatesGenerated();
        }
        return -1;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getDistinctStatesGenerated()
     */
    @Override
    public long getDistinctStatesGenerated() {
        if (tlcServer.isRunning()) {
            final IFPSetManager fpSetManager = tlcServer.getFPSetManager();
            if (fpSetManager != null) {
                return fpSetManager.size();
            }
        }
        return -1;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getStateQueueSize()
     */
    @Override
    public long getStateQueueSize() {
        return tlcServer.getNewStates();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getStatesGeneratedPerMinute()
     */
    @Override
    public long getStatesGeneratedPerMinute() {
        return tlcServer.getStatesGeneratedPerMinute();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getDistinctStatesGeneratedPerMinute()
     */
    @Override
    public long getDistinctStatesGeneratedPerMinute() {
        return tlcServer.getDistinctStatesGeneratedPerMinute();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getProgress()
     */
    @Override
    public int getProgress() {
        if (tlcServer.isRunning()) {
            try {
                return tlcServer.trace.getLevelForReporting();
            } catch (final IOException e) {
                e.printStackTrace();
            }
        }
        return -1;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getWorkerCount()
     */
    @Override
    public int getWorkerCount() {
        return tlcServer.getWorkerCount();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#checkpoint()
     */
    @Override
    public void checkpoint() {
        TLCGlobals.forceChkpt();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getAverageBlockCnt()
     */
    @Override
    public long getAverageBlockCnt() {
        return tlcServer.getAverageBlockCnt();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getRuntimeRatio()
     */
    @Override
    public double getRuntimeRatio() {
        // Distributed TLC does not support liveness checking
        return 0d;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#liveCheck()
     */
    @Override
    public void liveCheck() {
        // Distributed TLC does not support liveness checking
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getCurrentState()
     */
    @Override
    public String getCurrentState() {
        final TLCState state = tlcServer.stateQueue.sPeek();
        if (state != null) {
            return state.toString();
        }
        return "N/A";
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getSpecName()
     */
    @Override
    public String getSpecName() {
        if (tlcServer.isRunning()) {
            try {
                return tlcServer.getSpecFileName();
            } catch (final RemoteException e) {
                e.printStackTrace();
            }
        }
        return "N/A";
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getModelName()
     */
    @Override
    public String getModelName() {
        if (tlcServer.isRunning()) {
            try {
                return tlcServer.getConfigFileName();
            } catch (final RemoteException e) {
                e.printStackTrace();
            }
        }
        return "N/A";
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#stop()
     */
    @Override
    public void stop() {
        synchronized (tlcServer) {
            tlcServer.setDone();

            try {
                tlcServer.stateQueue.close();
            } catch (Exception e) {
            }

            tlcServer.notifyAll();
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#suspend()
     */
    @Override
    public void suspend() {
        synchronized (tlcServer) {
            tlcServer.stateQueue.suspendAll();
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#resume()
     */
    @Override
    public void resume() {
        synchronized (tlcServer) {
            tlcServer.stateQueue.resumeAll();
        }
    }
}
