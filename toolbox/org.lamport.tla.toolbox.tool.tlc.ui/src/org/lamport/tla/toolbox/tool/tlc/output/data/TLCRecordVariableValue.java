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

/**
 * @author Simon Zambrovski
 */
public class TLCRecordVariableValue extends TLCVariableValue implements TLCMultiVariableValue {

    private static final String[] DELIMETERS = { "[", ",", "]" };

    /**
     * @param recordPairs
     */
	public TLCRecordVariableValue(List<TLCVariableValue> recordPairs) {
        this.value = recordPairs;
    }

	public TLCNamedVariableValue[] getPairs() {
		return (TLCNamedVariableValue[]) ((List<TLCNamedVariableValue>) this.value)
				.toArray(new TLCNamedVariableValue[((List<TLCNamedVariableValue>) this.value).size()]);
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue#getValue()
	 */
	public Object getValue() {
		return getPairs();
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue#toSimpleString()
	 */
	public String toSimpleString() {
		return arrayToSimpleStringBuffer(getPairs(), DELIMETERS).toString();
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
