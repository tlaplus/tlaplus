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
 *   Leslie Lamport - initial API and implementation
 ******************************************************************************/

package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.List;

/*************************************************************
 * Represents a function as a list of TLCFcnElementVariable objects
 * 
 * @author Leslie Lamport
 */
public class TLCFunctionVariableValue extends TLCVariableValue implements TLCMultiVariableValue {

    private static final String[] DELIMETERS = { "(", " @@", ")" };
    private final TLCFcnElementVariableValue[] elements;
    
    /**
     * @param fcnElements
     */
	public TLCFunctionVariableValue(List fcnElements) {
		this.value = fcnElements;
		this.elements = innerGetFcnElements();
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue#getValue()
	 */
	public Object getValue() {
		return elements;
	}

	public TLCFcnElementVariableValue[] getFcnElements() {
		return elements;
	}

	public TLCFcnElementVariableValue[] innerGetFcnElements() {
		return (TLCFcnElementVariableValue[]) ((List) this.value)
				.toArray(new TLCFcnElementVariableValue[((List) this.value).size()]);
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue#toSimpleString()
	 */
	public String toSimpleString() {
		return arrayToSimpleStringBuffer(getFcnElements(), DELIMETERS).toString();
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
