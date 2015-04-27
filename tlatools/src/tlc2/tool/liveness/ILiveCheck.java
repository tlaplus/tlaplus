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

	/**
	 * No states can be added with add*State once finalCheck has been called.
	 * 
	 * @see ILiveCheck#check()
	 * @return
	 * @throws Exception
	 */
	boolean finalCheck() throws Exception;

	/* simulation mode */
	
	/**
	 * This method is the mutual exclusive counterpart to addInitState and
	 * addNextState. Where the two each take a single state and its successors,
	 * checkTrace expects a sequence of TLCStates. The first state in this sequence
	 * is seen as the init state whereas the remaining states in the sequence belong
	 * to the behavior started by the init state.
	 * <p>
	 * checkTrace behaves similar to adding the sequence's first state with addInitState
	 * and the others with addNextState. However, checkTrace is meant to be used
	 * in simulation mode (see Simulator) only. Don't call check or finalCheck, it
	 * is done as part of checkTrace.
	 * <p>
	 * checkTrace can be called multiple times until ILiveCheck has been closed (see close()).
	 * 
	 * @param trace
	 * @throws IOException
	 * @throws InterruptedException
	 */
	void checkTrace(final StateVec trace) throws IOException, InterruptedException;
	
	/* auxiliary methods */
	
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

	void reset() throws IOException;
}