// Copyright (c) Jan 4, 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.management;

import java.io.IOException;
import java.rmi.RemoteException;

import javax.management.NotCompliantMBeanException;

import tlc2.tool.ModelChecker;
import tlc2.tool.distributed.management.TLCStatisticsMXBean;

/**
 * @author Markus Alexander Kuppe
 */
public class ModelCheckerMXWrapper extends TLCStandardMBean implements TLCStatisticsMXBean {

	private final ModelChecker modelChecker;

	public ModelCheckerMXWrapper(final ModelChecker aModelChecker)
			throws NotCompliantMBeanException {
		super(TLCStatisticsMXBean.class);
		this.modelChecker = aModelChecker;
		// register all TLCStatisticsMXBeans under the same name
		registerMBean("tlc2.tool:type=ModelChecker");
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getStatesGenerated()
	 */
	public long getStatesGenerated() {
		return modelChecker.getStatesGenerated();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getDistinctStatesGenerated()
	 */
	public long getDistinctStatesGenerated() {
		return modelChecker.theFPSet.size();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getStateQueueSize()
	 */
	public long getStateQueueSize() {
		return modelChecker.theStateQueue.size();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getStatesGeneratedPerMinute()
	 */
	public long getStatesGeneratedPerMinute() {
		return modelChecker.statesPerMinute;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getDistinctStatesGeneratedPerMinute()
	 */
	public long getDistinctStatesGeneratedPerMinute() {
		return modelChecker.distinctStatesPerMinute;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getProgress()
	 */
	public int getProgress() {
		try {
			return modelChecker.trace.getLevelForReporting();
		} catch (IOException e) {
			e.printStackTrace();
			return -1;
		}
	}
}
