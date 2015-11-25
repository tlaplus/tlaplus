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

public class TLCSequenceVariableValue extends TLCVariableValue implements TLCMultiVariableValue {

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
		 * SEQUENCES In general, it's not clear how differences between two
		 * sequences should be highlighted. We adopt the following
		 * preliminary approach: If one sequence is a proper initial prefix
		 * or suffix of the other, then the difference is interpreted as
		 * adding or deleting the appropriate sequence elements. Otherwise,
		 * the sequences are treated as functions.
		 * 
		 * Note: If one sequence is both an initial prefix and a suffix of
		 * the other then we give preference to interpreting the operation
		 * as adding to the end or removing from the front.
		 */
		if (!(other instanceof TLCSequenceVariableValue)) {
			return;
		}
		TLCFcnElementVariableValue[] firstElts = this.getElements();
		TLCFcnElementVariableValue[] secondElts = ((TLCSequenceVariableValue) other).getElements();
		if (firstElts.length == secondElts.length) {
			setFcnElementArrayDiffInfo(firstElts, secondElts);
			return;
		}

		TLCFcnElementVariableValue[] shorter = firstElts;
		TLCFcnElementVariableValue[] longer = secondElts;
		boolean firstShorter = true;
		if (firstElts.length > secondElts.length) {
			longer = firstElts;
			shorter = secondElts;
			firstShorter = false;
		}
		boolean isPrefix = true;
		for (int i = 0; i < shorter.length; i++) {
			if (!((TLCVariableValue) shorter[i].getValue()).toSimpleString()
					.equals(((TLCVariableValue) longer[i].getValue()).toSimpleString())) {
				isPrefix = false;
				break;
			}
		}
		boolean isSuffix = true;
		for (int i = 0; i < shorter.length; i++) {
			if (!((TLCVariableValue) shorter[i].getValue()).toSimpleString().equals(
					((TLCVariableValue) longer[i + longer.length - shorter.length].getValue()).toSimpleString())) {

				isSuffix = false;
				break;
			}
		}
		/*
		 * If it's both a prefix and a suffix, we interpret the change as
		 * either adding to the end or deleting from the front. If it's
		 * neither, we treat the sequences as functions.
		 */
		if (isPrefix && isSuffix) {
			if (firstShorter) {
				isSuffix = false;
			} else {
				isPrefix = false;
			}
		} else if (!(isPrefix || isSuffix)) {
			setFcnElementArrayDiffInfo(firstElts, secondElts);
			return;
		}
	}
}
