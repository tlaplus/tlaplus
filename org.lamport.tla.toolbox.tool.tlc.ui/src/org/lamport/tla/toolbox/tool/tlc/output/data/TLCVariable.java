package org.lamport.tla.toolbox.tool.tlc.output.data;

public class TLCVariable
{
    private String name;
    private TLCVariableValue value;
    private boolean isTraceExplorerVar;

    public TLCVariable(String name, TLCVariableValue value)
    {
        this.name = name;
        this.value = value;
        this.isTraceExplorerVar = false;

    }

    public String getName()
    {
        return name;
    }

    public TLCVariableValue getValue()
    {
        return value;
    }

    public String toString()
    {
        return value == null ? "" : value.toString();
    }

    public void setName(String name)
    {
        this.name = name;
    }

    public void setValue(TLCVariableValue value)
    {
        this.value = value;
    }

    /**
     * Returns whether or not this variable represents
     * a trace explorer expression. See {@link TLCVariable#setTraceExplorerVar(boolean)}
     * for setting the value returned by this method. By default, it is false.
     * @return
     */
    public boolean isTraceExplorerVar()
    {
        return isTraceExplorerVar;
    }

    /**
     * Returns the name this variable in a single line String.
     * 
     * The name could be multiple lines if this represents a trace explorer
     * expression.
     * 
     * @return
     */
    public String getSingleLineName()
    {
        return name.replaceAll("\n", "").replaceAll("\r", "");    }

    /**
     * Sets the status of this variable as representing or not
     * representing a trace explorer expression. By default, it
     * is not.
     * 
     * @param isTraceExplorerVar whether or not this variable
     * represents a trace explorer expression.
     */
    public void setTraceExplorerVar(boolean isTraceExplorerVar)
    {
        this.isTraceExplorerVar = isTraceExplorerVar;
    }

}
