package org.lamport.tla.toolbox.tool.tlc.output.data;

/**
 * Represents a pair of TLCVariableValue objects; used to hold individual
 * mappings of a function--the individual ordered pairs if a function were
 * a set of ordered pairs.  The object O represents O.from @@ O.value
 * @author Leslie Lamport
 * @version $Id$
 */
public class TLCFcnElementVariableValue extends TLCVariableValue
{
    protected TLCVariableValue from;

    public TLCVariableValue getFrom()
    {
        return from;
    }

    /**
     * 
     */
    public TLCFcnElementVariableValue(TLCVariableValue fromVal, TLCVariableValue toVal)
    {
        from = fromVal;
        value = toVal;
    }

    public String toString()
    {
        return from.toString() + " :>" + value.toString();
    }

    public String toSimpleString()
    {
        return from.toSimpleString() + " :>" + ((TLCVariableValue) value).toSimpleString();
    }

}
