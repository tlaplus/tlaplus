package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.List;

public class TLCSequenceVariableValue extends TLCVariableValue
{

    private static final String[] DELIMETERS = { "<<", ",", ">>" };

    /*
     * Need to keep the value as an array of TLCFcnElementVariableValue 
     * objects rather than computing them afresh because those objects
     * can be stored in the HashSets that determine highlighting of an
     * error trace.  
     */
    private TLCFcnElementVariableValue[] elements;
    
    TLCSequenceVariableValue(List values)
    {
        this.value = values;
        this.elements = this.innerGetElements();
    }

    public Object getValue()
    {
        return getElements();
    }

    public TLCFcnElementVariableValue[] getElements() {
        return elements;
    }
 
    private TLCFcnElementVariableValue[] innerGetElements() {
        List list = (List) value;

        TLCFcnElementVariableValue[] result = new TLCFcnElementVariableValue[list.size()];
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
