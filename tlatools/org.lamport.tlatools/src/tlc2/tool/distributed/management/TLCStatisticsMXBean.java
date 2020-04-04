// Copyright (c) Jan 4, 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.distributed.management;

import tlc2.tool.ModelChecker;
import tlc2.tool.TLCState;

/**
 * @author Markus Alexander Kuppe
 */
public interface TLCStatisticsMXBean {

	/**
	 * @return The version of TLC.
	 */
	String getVersion();
	
	/**
	 * @return The code revision corresponding to this version of TLC.
	 */
	String getRevision();
	
	/**
	 * @return The amount of states generated (non-distinct).
	 *         {@link TLCStatisticsMXBean#getStatesGenerated()} >=
	 *         {@link TLCStatisticsMXBean#getDistinctStatesGenerated()}
	 */
	long getStatesGenerated();

	/**
	 * @return The amount of distinct states found (= amount of fingerprints)
	 */
	long getDistinctStatesGenerated();

	/**
	 * @return The amount of new states
	 */
	long getStateQueueSize();

	/**
	 * @return The state generation rate per minute (spm)
	 */
	long getStatesGeneratedPerMinute();

	/**
	 * @return The distinct state generation rate per minute (dspm)
	 */
	long getDistinctStatesGeneratedPerMinute();
	
	/**
	 * @return The depth of the state graph
	 */
	int getProgress();
	
	/**
	 * @return The number of workers
	 */
	int getWorkerCount();
	
	/**
	 * @return Average block count handed out to workers as units of work
	 */
	long getAverageBlockCnt();
	
	/**
	 * Creates a checkpoint next time possible
	 */
	void checkpoint();
	
	/**
	 * @return The ratio between time dedicated to safety and liveness checking.
	 */
	double getRuntimeRatio();
	
	/**
	 * Force new progress interval to check liveness
	 */
	void liveCheck();
	
	/**
	 * The string representation of a {@link TLCState} the {@link ModelChecker}
	 * has recently checked.
	 */
	String getCurrentState();
	
	/**
	 * @return The name of the spec currently being checked by TLC.
	 */
	String getSpecName();
	
	/**
	 * @return The name of the model curreclty being checked by TLC.
	 */
	String getModelName();

	/**
	 * Force TLC to stop model checking.
	 */
	void stop();
	
	/**
	 * Suspend model checking until resume is called.
	 */
	void suspend();
	
	/**
	 * Resumes model checking after a suspend. Do not resume an running model checker.
	 * It could interfere with model checking.
	 */
	void resume();
}
