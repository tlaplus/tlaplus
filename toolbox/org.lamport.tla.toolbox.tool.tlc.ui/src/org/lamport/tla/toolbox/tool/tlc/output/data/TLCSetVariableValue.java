/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Simon Zambrovski - initial API and implementation
 ******************************************************************************/

package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.List;

public class TLCSetVariableValue extends TLCVariableValue implements TLCMultiVariableValue {

    private static final String[] DELIMETERS = { "{", ",", "}" };

	TLCSetVariableValue(List values) {
        this.value = values;
    }

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue#getValue()
	 */
	public Object getValue() {
        return getElements();
    }

	public TLCVariableValue[] getElements() {
		List list = (List) value;
		return (TLCVariableValue[]) list.toArray(new TLCVariableValue[list.size()]);
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue#toSimpleString()
	 */
	public String toSimpleString() {
		TLCVariableValue[] elements = getElements();
		return arrayToSimpleStringBuffer(elements, DELIMETERS).toString();
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCMultiVariableValue#asList()
	 */
	public List<TLCVariableValue> asList() {
		return (List<TLCVariableValue>) this.value;
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
