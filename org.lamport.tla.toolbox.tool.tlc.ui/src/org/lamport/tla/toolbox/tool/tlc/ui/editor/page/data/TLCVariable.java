package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data;

public class TLCVariable
{
    private String name;
    private TLCVariableValue value;

    public TLCVariable(String name, TLCVariableValue value)
    {
        this.name = name;
        this.value = value;

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
    
    
}
