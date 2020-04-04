// Copyright (c) Jan 4, 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.distributed.management;

import java.io.IOException;
import java.rmi.RemoteException;

import javax.management.NotCompliantMBeanException;

import tlc2.TLCGlobals;
import tlc2.tool.TLCState;
import tlc2.tool.distributed.TLCServer;
import tlc2.tool.distributed.fp.IFPSetManager;
import tlc2.tool.management.TLCStandardMBean;

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
	public long getStatesGenerated() {
		if (tlcServer.isRunning()) {
			return tlcServer.getStatesGenerated();
		}
		return -1;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getDistinctStatesGenerated()
	 */
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
	public long getStateQueueSize() {
		return tlcServer.getNewStates();
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getStatesGeneratedPerMinute()
	 */
	public long getStatesGeneratedPerMinute() {
		return tlcServer.getStatesGeneratedPerMinute();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getDistinctStatesGeneratedPerMinute()
	 */
	public long getDistinctStatesGeneratedPerMinute() {
		return tlcServer.getDistinctStatesGeneratedPerMinute();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getProgress()
	 */
	public int getProgress() {
		if (tlcServer.isRunning()) {
			try {
					return tlcServer.trace.getLevelForReporting();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		return -1;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getWorkerCount()
	 */
	public int getWorkerCount() {
		return tlcServer.getWorkerCount();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#checkpoint()
	 */
	public void checkpoint() {
		TLCGlobals.forceChkpt();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getAverageBlockCnt()
	 */
	public long getAverageBlockCnt() {
		return tlcServer.getAverageBlockCnt();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getRuntimeRatio()
	 */
	public double getRuntimeRatio() {
		// Distributed TLC does not support liveness checking
		return 0d;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#liveCheck()
	 */
	public void liveCheck() {
		// Distributed TLC does not support liveness checking
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getCurrentState()
	 */
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
	public String getSpecName() {
		if (tlcServer.isRunning()) {
			try {
				return tlcServer.getSpecFileName();
			} catch (RemoteException e) {
				e.printStackTrace();
			}
		}
		return "N/A";
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getModelName()
	 */
	public String getModelName() {
		if (tlcServer.isRunning()) {
			try {
				return tlcServer.getConfigFileName();
			} catch (RemoteException e) {
				e.printStackTrace();
			}
		}
		return "N/A";
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#stop()
	 */
	public void stop() {
		synchronized (tlcServer) {
			tlcServer.setDone();
			tlcServer.stateQueue.finishAll();
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
