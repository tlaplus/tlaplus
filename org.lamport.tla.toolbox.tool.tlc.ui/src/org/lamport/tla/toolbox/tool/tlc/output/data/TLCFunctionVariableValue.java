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
    private TLCFcnElementVariableValue[] elements;
    /**
     * @param fcnElements
     */
    public TLCFunctionVariableValue(List fcnElements)
    {
        this.value = fcnElements;
        this.elements = innerGetFcnElements();
    }

    public Object getValue()
    {
        return elements;
    }

    public TLCFcnElementVariableValue[] getFcnElements() {
        return elements;
    }
    public TLCFcnElementVariableValue[] innerGetFcnElements()
    {
        return (TLCFcnElementVariableValue[]) ((List) this.value)
                .toArray(new TLCFcnElementVariableValue[((List) this.value).size()]);
    }

    public String toSimpleString()
    {
        return arrayToSimpleStringBuffer(getFcnElements(), DELIMETERS).toString();
    }

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue#innerDiff(org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue)
	 */
	protected void innerDiff(TLCVariableValue other) {
		/*
		 * FUNCTIONS We mark a record element as added or deleted if its
		 * label does not appear in one of the elements of the other record.
		 * We mark the element as changed, and call setInnerDiffInfo on the
		 * elements' values if elements with same label but different values
		 * appear in the two records.
		 */
		if (!(other instanceof TLCFunctionVariableValue)) {
			return;
		}

		setFcnElementArrayDiffInfo(this.elements, ((TLCFunctionVariableValue) other).elements);
	}
}
