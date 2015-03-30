package tlc2.tool.liveness;

import java.io.IOException;

import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import tlc2.util.LongVec;
import tlc2.util.statistics.IBucketStatistics;

public interface ILiveCheck {

	/**
	 * This method records that state is an initial state in the behavior graph.
	 * It is called when a new initial state is generated.
	 */
	void addInitState(TLCState state, long stateFP);

	/**
	 * This method adds new nodes into the behavior graph induced by s0. It is
	 * called after the successors of s0 are computed.
	 */
	void addNextState(TLCState s0, long fp0, StateVec nextStates, LongVec nextFPs) throws IOException;

	/**
	 * Check liveness properties for the current partial state graph. Returns
	 * true iff it finds no errors.
	 */
	boolean check() throws Exception;

	boolean finalCheck() throws Exception;

	String getMetaDir();

	Tool getTool();

	IBucketStatistics getOutDegreeStatistics();

	ILiveChecker getChecker(int idx);

	int getNumChecker();

	/* Close all the files for disk graphs. */
	void close() throws IOException;

	/* Checkpoint. */
	void beginChkpt() throws IOException;

	void commitChkpt() throws IOException;

	void recover() throws IOException;

	IBucketStatistics calculateInDegreeDiskGraphs(IBucketStatistics aGraphStats) throws IOException;

	IBucketStatistics calculateOutDegreeDiskGraphs(IBucketStatistics aGraphStats) throws IOException;

}