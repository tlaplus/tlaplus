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
        MP.printState(EC.TLC_STATE_PRINT1, new String[] { String.valueOf(num), stateString });
    }

    /**
     * Prints the state with number
     */
    public static void printState(TLCState currentState, int num)
    {
        MP.printState(EC.TLC_STATE_PRINT1, new String[] { String.valueOf(num), currentState.toString() });
    }

    /**
     * Prints the state
     */
    public static void printState(TLCState currentState)
    {
        MP.printState(EC.TLC_STATE_PRINT1, new String[] { "", currentState.toString() });
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
                stateString });
    }

    /**
     * Reports that the state with a given number is stuttering
     */
    public static void printStutteringState(int num)
    {
        MP.printState(EC.TLC_STATE_PRINT3, new String[] { String.valueOf(num) });
    }

}
