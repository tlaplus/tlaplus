package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.List;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCRecordVariableValue extends TLCVariableValue
{

    private static final String[] DELIMETERS = { "[", ",", "]" };

    /**
     * @param recordPairs
     */
    public TLCRecordVariableValue(List recordPairs)
    {
        this.value = recordPairs;
    }

    public TLCNamedVariableValue[] getPairs()
    {
        return (TLCNamedVariableValue[]) ((List) this.value).toArray(new TLCNamedVariableValue[((List) this.value)
                .size()]);
    }

    public Object getValue()
    {
        return getPairs();
    }

    public String toSimpleString()
    {
        return arrayToSimpleStringBuffer(getPairs(), DELIMETERS).toString();
    }
}
