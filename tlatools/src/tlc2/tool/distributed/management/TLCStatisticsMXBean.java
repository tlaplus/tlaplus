// Copyright (c) Jan 4, 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.distributed.management;

/**
 * @author Markus Alexander Kuppe
 */
/**
 * @author markus
 *
 */
public interface TLCStatisticsMXBean {

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
}
