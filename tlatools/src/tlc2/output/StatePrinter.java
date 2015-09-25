package tlc2.output;

import tlc2.TLCGlobals;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;

/**
 * Helper for printing states
 * @author Simon Zambrovski
 * @version $Id$
 */
public class StatePrinter
{
    /**
     * Prints the state information
     * if the TLC runs in print-diff-only mode and the last state is set, it will print the diff only 
     */
    public static void printState(TLCState currentState, TLCState lastState, int num)
    {
        String stateString;
        /* Added by rjoshi. */
        if (lastState != null && TLCGlobals.printDiffsOnly)
        {
            stateString = currentState.toString(lastState);
        } else
        {
            stateString = currentState.toString();
        }
        MP.printState(EC.TLC_STATE_PRINT1, new String[] { String.valueOf(num), stateString }, currentState, num);
    }

    /**
     * Prints the state with number
     */
    public static void printState(TLCState currentState, int num)
    {
        MP.printState(EC.TLC_STATE_PRINT1, new String[] { String.valueOf(num), currentState.toString() }, currentState, num);
    }

    /**
     * Prints the state
     */
    public static void printState(TLCState currentState)
    {
        MP.printState(EC.TLC_STATE_PRINT1, new String[] { "", currentState.toString() }, currentState, -1);
    }

    public static void printState(TLCStateInfo currentStateInfo) {
    	if (currentStateInfo.predecessorState == null) {
    		// It's an initial state
			printState(currentStateInfo, null, (int) currentStateInfo.stateNumber);
    	} else {
			printState(currentStateInfo, currentStateInfo.predecessorState.state, (int) currentStateInfo.stateNumber);
    	}
    }
    
    /**
     * Prints the state information
     * if the TLC runs in print-diff-only mode and the last state is set, it will print the diff only 
     */
    public static void printState(TLCStateInfo currentStateInfo, TLCState lastState, int num)
    {
        String stateString;

        /* Added by rjoshi. */
        if (lastState != null && TLCGlobals.printDiffsOnly)
        {
            stateString = currentStateInfo.state.toString(lastState);
        } else
        {
            stateString = currentStateInfo.state.toString();
        }
        MP.printState(EC.TLC_STATE_PRINT2, new String[] { String.valueOf(num), currentStateInfo.info.toString(),
                stateString }, currentStateInfo, num);
    }

    /**
     * Reports that the state with a given number is stuttering
     */
    public static void printStutteringState(int num)
    {
        MP.printState(EC.TLC_STATE_PRINT3, new String[] { String.valueOf(num + 1) }, (TLCState) null, num + 1);
    }

	/**
	 * Prints a marker (EC.TLC_BACK_TO_STATE) looping back to the state with the
	 * given stateNum.
	 * @param currentStateInfo 
	 * 
	 * @param stateNum
	 */
	public static void printBackToState(final TLCStateInfo currentStateInfo, final long stateNum) {
		if (TLCGlobals.tool) {
			MP.printState(EC.TLC_BACK_TO_STATE, new String[] { "" + stateNum, currentStateInfo.info.toString() }, (TLCState) null, -1);
		} else {
			MP.printMessage(EC.TLC_BACK_TO_STATE, new String[] {"" + stateNum, currentStateInfo.info.toString()});
		}
	}
}
