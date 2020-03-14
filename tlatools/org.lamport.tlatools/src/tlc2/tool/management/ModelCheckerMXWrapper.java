// Copyright (c) Jan 4, 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.management;

import javax.management.NotCompliantMBeanException;

import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.tool.ModelChecker;
import tlc2.tool.TLCState;
import tlc2.tool.distributed.management.TLCStatisticsMXBean;
import tlc2.tool.fp.DiskFPSet;

/**
 * @author Markus Alexander Kuppe
 */
public class ModelCheckerMXWrapper extends TLCStandardMBean implements TLCStatisticsMXBean {

	public static final String OBJ_NAME = "tlc2.tool:type=ModelChecker";

	private final ModelChecker modelChecker;
	private final TLC tlc;

	public ModelCheckerMXWrapper(final ModelChecker aModelChecker, final TLC tlc)
			throws NotCompliantMBeanException {
		super(TLCStatisticsMXBean.class);
		this.modelChecker = aModelChecker;
		this.tlc = tlc;
		// register all TLCStatisticsMXBeans under the same name
		registerMBean(OBJ_NAME);
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
		return modelChecker.getStateQueueSize();
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
		return modelChecker.getProgress();
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

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getRuntimeRatio()
	 */
	public double getRuntimeRatio() {
		return modelChecker.getRuntimeRatio();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#liveCheck()
	 */
	public void liveCheck() {
		modelChecker.forceLiveCheck();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getCurrentState()
	 */
	public String getCurrentState() {
		final TLCState state = modelChecker.theStateQueue.sPeek();
		if (state != null) {
			return state.toString();
		}
		return "N/A";
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getSpecName()
	 */
	public String getSpecName() {
		return tlc.getSpecName();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#getModelName()
	 */
	public String getModelName() {
		return tlc.getModelName();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#stop()
	 */
	public void stop() {
		modelChecker.stop();
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#suspend()
	 */
	public void suspend() {
		modelChecker.suspend();
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.management.TLCStatisticsMXBean#resume()
	 */
	public void resume() {
		modelChecker.resume();
	}
}
