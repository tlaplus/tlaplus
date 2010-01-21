package org.lamport.tla.toolbox.tool.tlc.traceexplorer;

import org.lamport.tla.toolbox.tool.tlc.launch.TraceExplorerDelegate;

/**
 * A class for representing the elements of a TLC variable
 * that are necessary for the launch delegate for the trace explorer.
 * Currently, this launch delegate is {@link TraceExplorerDelegate}.
 * 
 * This class contains the variable name as a string and a string
 * representation of the variable value.
 * 
 * @author Daniel Ricketts
 *
 */
public class SimpleTLCVariable
{

    private String varName;
    private String valueAsString;

    /**
     * Constructor.
     * 
     * @param varName name of the variable
     * @param valueAsString TLC string representation of the variable value
     */
    public SimpleTLCVariable(String varName, String valueAsString)
    {
        this.varName = varName;
        this.valueAsString = valueAsString;
    }

    public String getVarName()
    {
        return varName;
    }

    public String getValueAsString()
    {
        return valueAsString;
    }

}
