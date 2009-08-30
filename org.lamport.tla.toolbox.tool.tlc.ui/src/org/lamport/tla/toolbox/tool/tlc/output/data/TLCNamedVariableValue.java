package org.lamport.tla.toolbox.tool.tlc.output.data;

/**
 * Represents named values
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCNamedVariableValue extends TLCVariableValue
{

    private String name;

    TLCNamedVariableValue(String name, TLCVariableValue value)
    {
        this.name = name;
        this.value = value;
    }

    public String getName()
    {
        return name;
    }

    public String toString()
    {
        return this.name + " |-> " + value.toString();  
    }
    
    public String toSimpleString()
    {
        return this.name + " |-> " + ( (TLCVariableValue) value).toSimpleString();  
    }
}
