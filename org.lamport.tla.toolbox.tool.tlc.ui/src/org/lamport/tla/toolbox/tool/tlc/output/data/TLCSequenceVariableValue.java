package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.List;

public class TLCSequenceVariableValue extends TLCVariableValue
{

    private static final String[] DELIMETERS = { "<<", ",", ">>" };

    /*
     * Need to keep the following two values as arrays of objects 
     * rather than computing them afresh because those objects
     * can be stored in the HashSets that determine highlighting of an
     * error trace.  
     */
    /**
     * The list of sequence values represented as function elements
     * 1 :> v1, 2 :> v2, ... .  We return these as the sequence's children 
     * because that allows them to be displayed in the error trace in a 
     * more useful way.
     */
    private TLCFcnElementVariableValue[] elements;

    /**  
     * The list of values of the sequence elements.
     */
    private TLCVariableValue[] elementValues;
    
    TLCSequenceVariableValue(List values)
    {
        this.value = values;
        this.elements = this.innerGetElements();
        elementValues = new TLCVariableValue[elements.length];
        for (int i = 0; i < elements.length; i++) {
            elementValues[i] = (TLCVariableValue) elements[i].getValue();
        }
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
        // Changed from using elements to using elementValues on 26 Oct 2009
        // so we don't print the "1:>", "2:>", ...
        return arrayToSimpleStringBuffer(elementValues, DELIMETERS).toString();
    }

}
