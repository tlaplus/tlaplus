package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.List;

/*************************************************************
 * Represents a function as a list of TLCFcnElementVariable objects
 * 
 * @author Leslie Lamport
 * @version $Id$
 */
public class TLCFunctionVariableValue extends TLCVariableValue
{

    private static final String[] DELIMETERS = { "(", " @@", ")" };

    /**
     * @param fcnElements
     */
    public TLCFunctionVariableValue(List fcnElements)
    {
        this.value = fcnElements;
    }

    public Object getValue()
    {
        return getFcnElements();
    }

    public TLCFcnElementVariableValue[] getFcnElements()
    {
        return (TLCFcnElementVariableValue[]) ((List) this.value)
                .toArray(new TLCFcnElementVariableValue[((List) this.value).size()]);
    }

    public String toSimpleString()
    {
        return arrayToSimpleStringBuffer(getFcnElements(), DELIMETERS).toString();
    }
}
