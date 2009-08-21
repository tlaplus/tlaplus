package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data;

import org.eclipse.core.runtime.Assert;

/**
 * A representation of a variable value
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class TLCVariableValue
{
    private static final String CB = "]";
    private static final String OB = "[";

    /**
     * Factory method to deliver simple values
     * @param string
     * @return
     */
    public static TLCVariableValue parseValue(String string)
    {
        Assert.isNotNull(string, "The value must be not null");
        string.trim();
        if (string.startsWith(OB) && string.endsWith(CB))
        {
            TLCVariableValue value = new TLCRecordVariableValue();
            value.value = string;
            return value;
        } else
        {

            TLCVariableValue value = new TLCSimpleVariableValue();
            value.value = string;
            return value;
        }
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
