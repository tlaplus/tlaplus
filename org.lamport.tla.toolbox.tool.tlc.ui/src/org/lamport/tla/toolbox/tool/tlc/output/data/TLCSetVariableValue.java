package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.List;

public class TLCSetVariableValue extends TLCVariableValue
{

    private static final String[] DELIMETERS = { "{", ",", "}" };

    TLCSetVariableValue(List values)
    {
        this.value = values;

    }

    public Object getValue()
    {
        return getElements();
    }

    public TLCVariableValue[] getElements()
    {
        @SuppressWarnings("unchecked")
		List<TLCVariableValue> list = (List<TLCVariableValue>) value;
        return list.toArray(new TLCVariableValue[list.size()]);
    }

    public String toSimpleString()
    {
        TLCVariableValue[] elements = getElements();
        return arrayToSimpleStringBuffer(elements, DELIMETERS).toString();
    }

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue#innerDiff(org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue)
	 */
	protected void innerDiff(TLCVariableValue other) {
		/*
		 * SETS For two sets, the only meaningful changes are additions and
		 * deletions.
		 */
		if (!(other instanceof TLCSetVariableValue)) {
			return;
		}
		TLCVariableValue[] firstElts = this.getElements();
		TLCVariableValue[] secondElts = ((TLCSetVariableValue) other).getElements();

		for (int i = 0; i < firstElts.length; i++) {
			boolean notfound = true;
			int j = 0;
			while (notfound && j < secondElts.length) {
				if (firstElts[i].toSimpleString().equals(secondElts[j].toSimpleString())) {
					notfound = false;
				}
				j++;
			}
			if (notfound) {
				firstElts[i].setDeleted();
			}
		}

		for (int i = 0; i < secondElts.length; i++) {
			boolean notfound = true;
			int j = 0;
			while (notfound && j < firstElts.length) {
				if (firstElts[j].toSimpleString().equals(secondElts[i].toSimpleString())) {
					notfound = false;
				}
				j++;
			}
			if (notfound) {
				secondElts[i].setAdded();
			}
		}
	}
}
