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

/**
 * Represents a pair of TLCVariableValue objects; used to hold individual
 * mappings of a function--the individual ordered pairs if a function were a set
 * of ordered pairs. The object O represents O.from @@ O.value
 * 
 * @author Leslie Lamport
 */
public class TLCFcnElementVariableValue extends TLCVariableValue {
    protected final TLCVariableValue from;

	public TLCVariableValue getFrom() {
        return from;
    }

	public TLCFcnElementVariableValue(TLCVariableValue fromVal, TLCVariableValue toVal) {
        from = fromVal;
        value = toVal;
    }

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue#toString()
	 */
	public String toString() {
        return from.toString() + " :> " + value.toString();
    }

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue#toSimpleString()
	 */
	public String toSimpleString() {
        return from.toSimpleString() + " :> " + ((TLCVariableValue) value).toSimpleString();
    }

}
