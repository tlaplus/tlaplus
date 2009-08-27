package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data;

/**
 * Represents simple values
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCSimpleVariableValue extends TLCVariableValue
{
    protected TLCSimpleVariableValue(Object value)
    {
        this.value = value;
    }

    public String toString()
    {
       return (String) this.value ;
    }

}
