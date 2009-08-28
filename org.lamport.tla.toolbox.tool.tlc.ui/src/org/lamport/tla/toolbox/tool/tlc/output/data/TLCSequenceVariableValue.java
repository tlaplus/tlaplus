package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.List;

public class TLCSequenceVariableValue extends TLCVariableValue
{

    private static final String[] DELIMETERS = { "<<", ",", ">>" };

    TLCSequenceVariableValue(List values)
    {
        this.value = values;
    }

    public Object getValue()
    {
        return getElements();
    }

    public TLCVariableValue[] getElements()
    {
        List list = (List) value;

        TLCVariableValue[] result = new TLCVariableValue[list.size()];
        for (int i = 0; i < result.length; i++)
        {
            result[i] = new TLCFcnElementVariableValue(new TLCSimpleVariableValue("" + (i + 1)),
                    (TLCVariableValue) list.get(i));
        }
        return result;
    }

    public String toSimpleString()
    {
        TLCVariableValue[] elements = getElements();
        return arrayToSimpleStringBuffer(elements, DELIMETERS).toString();
    }

}
