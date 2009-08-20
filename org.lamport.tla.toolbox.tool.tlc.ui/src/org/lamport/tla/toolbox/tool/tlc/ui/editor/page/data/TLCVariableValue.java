package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data;

public class TLCVariableValue
{
    public static TLCVariableValue parseValue(String string)
    {
        TLCVariableValue value = new TLCVariableValue();
        value.value = string;
        return value;
    }

    protected Object value;

    public Object getValue()
    {
        return value;
    }

    public String toString()
    {
        return value.toString();
    }
}
