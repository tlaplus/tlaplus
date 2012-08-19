// Copyright (c) Jan 4, 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.management;

import java.io.IOException;

import javax.management.NotCompliantMBeanException;

import tlc2.TLCGlobals;
import tlc2.tool.ModelChecker;
import tlc2.tool.distributed.management.TLCStatisticsMXBean;
import tlc2.tool.fp.DiskFPSet;

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
		// if impl is DiskFPSet we don't want to add to the lock contention on
		// the RWLock in DiskFPSet and thus compromise on reading dirty values
		// (acceptable for statistics/metrics)
		if(modelChecker.theFPSet instanceof DiskFPSet) {
			DiskFPSet diskFPSet = (DiskFPSet) modelChecker.theFPSet;
			return diskFPSet.getFileCnt() + diskFPSet.getTblCnt();
		}
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
			// The modelchecker trace file might be closed already (e.g. it
			// gets closed at the end of the modelchecker run)
			return -1;
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getWorkerCount()
	 */
	public int getWorkerCount() {
		return TLCGlobals.getNumWorkers();
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
		//TODO adapt once Workers can support units of work greater than 1 
		return 1;
	}
}
