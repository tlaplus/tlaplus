package tlc2.output;

import tlc2.TLCGlobals;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import util.ToolIO;

/**
 * Helper for printing states
 * @author Simon Zambrovski
 * @version $Id$
 */
public class StatePrinter
{
	private static final int STATE_OVERWRITE_INTERVAL = Integer.getInteger(StatePrinter.class.getName() + ".overwrite", -1);

	/**
	 * Prints a single state out of a larger error trace, when the error is not
	 * related to invalidation of an invariant. This would be used if, for
	 * example, TLC finds a step where not all variables have defined values.
	 * @param currentState The single state in the trace.
	 * @param num The index of the state in the trace, counting from one.
	 */
    public static void printRuntimeErrorStateTraceState(TLCState currentState, int num)
    {
        MP.printState(EC.TLC_STATE_PRINT1, new String[] { String.valueOf(num), currentState.toString() }, currentState, num);
    }

    /**
     * Prints a single state for error reporting purposes, for example if the
     * state is invalid in some way. Not to be used when printing states just
     * because an invariant has been violated.
     * @param currentState The state to print.
     */
    public static void printStandaloneErrorState(TLCState currentState)
    {
        MP.printState(EC.TLC_STATE_PRINT1, new String[] { "", currentState.toString() }, currentState, -1);
    }

    /**
     * Prints a single state out of a larger state trace, for use when an
     * invariant is violated.
     * @param currentStateInfo
     */
    public static void printInvariantViolationStateTraceState(TLCStateInfo currentStateInfo) {
    	if (currentStateInfo.state.isInitial()) {
    		// It's an initial state
			StatePrinter.printInvariantViolationStateTraceState(currentStateInfo, null, (int) currentStateInfo.stateNumber);
    	} else {
			StatePrinter.printInvariantViolationStateTraceState(currentStateInfo, currentStateInfo.state.getPredecessor(), (int) currentStateInfo.stateNumber);
    	}
    }
    
    /**
     * Prints a single state out of a larger state trace, for use when an
     * invariant is violated.
     * If the {@link TLCGlobals#printDiffsOnly} flag is set, will print state
     * diffs instead of full state.
     * @param currentStateInfo Information about the single state in the trace.
     * @param previousState The previous state in the trace for diff printing.
     * @param num The index of the state in the trace, counting from one.
     */
    public static void printInvariantViolationStateTraceState(TLCStateInfo currentStateInfo, TLCState previousState, int num)
    {
    	printInvariantViolationStateTraceState(currentStateInfo, previousState, num, false);
    }

    public static void printInvariantViolationStateTraceState(TLCStateInfo currentStateInfo, TLCState previousState, int num, final boolean isFinal)
    {
        final String stateString =
        		null != previousState && TLCGlobals.printDiffsOnly
        		? currentStateInfo.state.toString(previousState)
        		: currentStateInfo.state.toString();
 
		// Fingerprint can't be calculated when state is incomplete; just use a random value.
        final String fingerprint =
        		currentStateInfo.state.allAssigned()
        		? String.valueOf(currentStateInfo.fingerPrint())
        		: "-1";

		// Metadata is the state number/ordinal and action name/location that is printed
		// above the actual state (values to variables).
        final String[] metadata = new String[] {
				String.valueOf(num),
				currentStateInfo.info.toString(),
				stateString,
				fingerprint
        };

		final String message = MP.printState(EC.TLC_STATE_PRINT2, metadata, currentStateInfo, num);
		
		if (STATE_OVERWRITE_INTERVAL > 0) {
			try {
				Thread.sleep(STATE_OVERWRITE_INTERVAL);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
			if (!isFinal) {
				// Reset as many lines as MP.printState(...) wrote to stdout.
				int lines = (int) (message.chars().filter(x -> x == '\n').count() + 1);
				ToolIO.out.printf("%s", "\033[F\033[K".repeat(lines));
			}
		}
    }

    /**
     * Prints a marker for a stuttering state that concludes a liveness
     * counterexample error trace.
     * @param num The index of the state in the trace, counting from one.
     */
    public static void printStutteringState(int num)
    {
        MP.printState(EC.TLC_STATE_PRINT3, new String[] { String.valueOf(num + 1) }, (TLCState) null, num + 1);
    }

    /**
     * Prints a marker for a loopback (lasso) state that concludes a liveness
     * counterexample error trace.
     * @param currentStateInfo Info about the loopback state.
     * @param stateNum The index of the state in the trace, counting from one.
     */
	public static void printBackToState(final TLCStateInfo currentStateInfo, final int stateNum) {
		if (TLCGlobals.tool) {
			//TODO If the unit test suite runs with -tool mode always turned on, many tests fail because of a NPE.  The NPE results
			//from null passed here as TLCState, which eventually causes the NPE in tlc2.tool.TLCStateInfo.toString().  When I changed
			//this from printState to printMessage, nothing obvious broke. However, I suspect some corner case in the Toolbox breaks,
			//which is why I decided not to touch this. 
			MP.printState(EC.TLC_BACK_TO_STATE, new String[] { Integer.toString(stateNum), currentStateInfo.info.toString() }, (TLCState)null, stateNum);
		} else {
			MP.printMessage(EC.TLC_BACK_TO_STATE, new String[] {Integer.toString(stateNum), currentStateInfo.info.toString()});
		}
	}
}
