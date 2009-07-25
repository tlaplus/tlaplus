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
    /**
     * Prints the state information
     * if the TLC runs in print-diff-only mode and the last state is set, it will print the diff only 
     */
    public static void printState(TLCState currentState, TLCState lastState, int num)
    {
        ToolIO.out.println("STATE " + num + ":");

        /* Added by rjoshi. */
        if (lastState != null && TLCGlobals.printDiffsOnly)
        {
            ToolIO.out.println(currentState.toString(lastState));
        } else
        {
            ToolIO.out.println(currentState);
        }
    }

    /**
     * Prints the state information
     * if the TLC runs in print-diff-only mode and the last state is set, it will print the diff only 
     */
    public static void printState(TLCStateInfo currentStateInfo, TLCState lastState, int num)
    {
        ToolIO.out.println("STATE " + num + ": " + currentStateInfo.info);

        /* Added by rjoshi. */
        if (lastState != null && TLCGlobals.printDiffsOnly)
        {
            ToolIO.out.println(currentStateInfo.state.toString(lastState));
        } else
        {
            ToolIO.out.println(currentStateInfo.state);
        }
    }

    /**
     * Prints the state
     */
    public static void printState(TLCState currentState, int num)
    {
        ToolIO.out.println("STATE " + num + ":");
        ToolIO.out.println(currentState);
    }

    /**
     * Prints the state
     */
    public static void printState(TLCState currentState)
    {
        ToolIO.out.println("STATE :");
        ToolIO.out.println(currentState);
    }

    /**
     * @param i
     */
    public static void printStutteringState(int num)
    {
        ToolIO.out.println("STATE " + num + ": Stuttering");
    }

}
