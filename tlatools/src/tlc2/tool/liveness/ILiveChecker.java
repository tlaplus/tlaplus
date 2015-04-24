package tlc2.tool.liveness;

import java.io.IOException;

import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.util.BitVector;
import tlc2.util.LongVec;

public interface ILiveChecker {

	/**
	 * This method records that state is an initial state in the behavior graph.
	 * It is called when a new initial state is generated.
	 */
	void addInitState(TLCState state, long stateFP);

	/**
	 * This method adds new nodes into the behavior graph induced by s0. It is
	 * called after the successors of s0 are computed.
	 */
	void addNextState(TLCState s0, long fp0, StateVec nextStates, LongVec nextFPs, BitVector checkActionResults,
			boolean[] checkStateResults) throws IOException;

	AbstractDiskGraph getDiskGraph();

	OrderOfSolution getSolution();

}