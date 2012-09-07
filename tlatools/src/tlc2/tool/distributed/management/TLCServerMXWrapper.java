// Copyright (c) Jan 4, 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.distributed.management;

import java.io.IOException;

import javax.management.NotCompliantMBeanException;

import tlc2.TLCGlobals;
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
}
