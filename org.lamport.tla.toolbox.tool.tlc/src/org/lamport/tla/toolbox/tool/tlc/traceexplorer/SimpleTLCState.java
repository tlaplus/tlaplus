package org.lamport.tla.toolbox.tool.tlc.traceexplorer;

import java.util.Vector;

import org.lamport.tla.toolbox.tool.tlc.launch.TraceExplorerDelegate;

/**
 * A class for representing the elements of a TLC state that
 * are necessary for the launch delegate for the trace explorer.
 * Currently, this launch delegate is {@link TraceExplorerDelegate}.
 * 
 * This class contains an array of {@link SimpleTLCVariable}.
 * 
 * @author Daniel Ricketts
 *
 */
public class SimpleTLCState
{

    private SimpleTLCVariable[] vars;
    private boolean isStuttering;
    private boolean isBackToState;
    private int stateNumber;

    private static final String COLON = ":";
    private static final String CR = "\n";
    private static final String STUTTERING = "Stuttering";
    private static final String BACK_TO_STATE = "Back";
    private static final String AND = "/\\";
    private static final String EQ = " = ";

    /**
     * Constructor.
     * 
     * @param vars variables in this state.
     * @param isStuttering whether this is a stuttering state or not
     * @param isBackToState whether this is a back to state or not
     * @param stateNumber number of the state in the trace
     */
    public SimpleTLCState(SimpleTLCVariable[] vars, boolean isStuttering, boolean isBackToState, int stateNumber)
    {
        this.vars = vars;
        this.isStuttering = isStuttering;
        this.isBackToState = isBackToState;
        this.stateNumber = stateNumber;
    }

    public SimpleTLCVariable[] getVars()
    {
        return vars;
    }

    public boolean isStuttering()
    {
        return isStuttering;
    }

    public boolean isBackToState()
    {
        return isBackToState;
    }

    public int getStateNumber()
    {
        return stateNumber;
    }

    public static SimpleTLCState parseSimpleTLCState(String stateInputString)
    {
        // state number
        int index = stateInputString.indexOf(COLON);
        // multi line
        int index2 = stateInputString.indexOf(CR, index);
        if (index2 == -1)
        {
            index2 = stateInputString.length();
        }

        int stateNumber = Integer.parseInt(stateInputString.substring(0, index).trim());
        String label = stateInputString.substring(index + 1, index2);
        boolean isStuttering = label.indexOf(STUTTERING) != -1;
        boolean isBackToState = label.indexOf(BACK_TO_STATE) != -1;

        SimpleTLCVariable[] vars = null;

        if (!isBackToState && !isStuttering)
        {
            // string from which the variables can be parsed
            String variableInputString = stateInputString.substring(index2 + 1);
            vars = parseVariables(variableInputString);
        }

        return new SimpleTLCState(vars, isStuttering, isBackToState, stateNumber);
    }

    private static SimpleTLCVariable[] parseVariables(String variableInputString)
    {
        String[] lines = variableInputString.split(CR);
        Vector vars = new Vector();
        int index;

        // buffer for accumulating the state variable
        String[] stateVarString = null;

        // iterate line-wise
        for (int j = 0; j < lines.length; j++)
        {
            // find the index of the first /\ in the line
            index = lines[j].indexOf(AND);
            // adding the current line to the previous lines
            if (index != -1)
            {
                // there was something in the buffer for the state variable
                // found an empty line, which means that this is the end of the current state
                if (stateVarString != null)
                {
                    SimpleTLCVariable var = new SimpleTLCVariable(stateVarString[0], stateVarString[1]);
                    vars.add(var);
                }

                stateVarString = lines[j].substring(index + AND.length()).split(EQ);
            } else
            {
                // no index

                if (stateVarString != null)
                {
                    // either an empty line
                    stateVarString[1] += CR;
                    stateVarString[1] += lines[j];
                } else
                {
                    // the state has one variable only
                    stateVarString = lines[j].split(EQ);
                }
            }
        }

        // write the last one
        if (stateVarString != null)
        {
            SimpleTLCVariable var = new SimpleTLCVariable(stateVarString[0], stateVarString[1]);
            vars.add(var);
        }

        return (SimpleTLCVariable[]) vars.toArray(new SimpleTLCVariable[vars.size()]);
    }

}
