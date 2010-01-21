package org.lamport.tla.toolbox.tool.tlc.traceexplorer;

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

}
