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

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue#innerDiff(org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue)
	 */
	protected void innerDiff(TLCVariableValue other) {
		/*
		 * RECORDS We mark a record element as added or deleted if its label
		 * does not appear in one of the elements of the other record. We
		 * mark the element as changed, and call setInnerDiffInfo on the
		 * elements' values if elements with same label but different values
		 * appear in the two records.
		 */
		if (!(other instanceof TLCRecordVariableValue)) {
			return;
		}
		TLCVariableValue[] firstElts = this.getPairs();
		TLCVariableValue[] secondElts = ((TLCRecordVariableValue) other).getPairs();

		String[] firstLHStrings = new String[firstElts.length];
		for (int i = 0; i < firstElts.length; i++) {
			firstLHStrings[i] = ((TLCNamedVariableValue) firstElts[i]).getName();
		}
		String[] secondLHStrings = new String[secondElts.length];
		for (int i = 0; i < secondElts.length; i++) {
			secondLHStrings[i] = ((TLCNamedVariableValue) secondElts[i]).getName();
		}

		setElementArrayDiffInfo(firstElts, firstLHStrings, secondElts, secondLHStrings);
	}
}
