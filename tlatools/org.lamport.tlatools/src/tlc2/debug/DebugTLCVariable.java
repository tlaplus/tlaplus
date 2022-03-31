/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.debug;

import java.util.List;
import java.util.Random;

import org.eclipse.lsp4j.debug.Variable;

import tlc2.value.impl.Enumerable;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.TLCVariable;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import util.UniqueString;

public class DebugTLCVariable extends Variable implements tlc2.value.impl.TLCVariable, Comparable<DebugTLCVariable> {
	
	private transient Value tlcValue;
	
	public DebugTLCVariable(UniqueString lhs) {
		this.setName(lhs.toString());
	}
	
	public DebugTLCVariable(String lhs) {
		this.setName(lhs);
	}
	
	public DebugTLCVariable(Value value) {
		this.setName(value.toString());
	}

	@Override
	public List<TLCVariable> getNested(Random rnd) {
		return this.tlcValue.getTLCVariables(this, rnd);
	}

	@Override
	public DebugTLCVariable setInstance(Value v) {
		this.tlcValue = v;
		return this;
	}

	@Override
	public TLCVariable newInstance(final String name, Value v, Random rnd) {
		DebugTLCVariable variable = new DebugTLCVariable(name);
		variable.setInstance(v);
		if (v instanceof Enumerable || v instanceof FcnRcdValue || v instanceof RecordValue || v instanceof TupleValue) {
			variable.setVariablesReference(rnd.nextInt(Integer.MAX_VALUE-1)+ 1);
		}
		return v.toTLCVariable(variable, rnd);
	}

	@Override
	public TLCVariable newInstance(Value value, Random rnd) {
		return newInstance(value.toString(), value, rnd);
	}
	
	@Override
	public Value getTLCValue() {
		return tlcValue;
	}

	@Override
	public int compareTo(DebugTLCVariable other) {
		if (getName().compareTo(other.getName()) != 0) {
			return getName().compareTo(other.getName());
		}
		if (getType().compareTo(other.getType()) != 0) {
			return getType().compareTo(other.getType());
		}
		if (getValue().compareTo(other.getValue()) != 0) {
			return getValue().compareTo(other.getValue());
		}
		// We do *not* compare tlcValue here for two reasons:
		// 1. tlcValue is marked transient, and, thus, might be null
		// 2. tlcValues representing infinite domains throw an exception when compared
		return 0;
	}
}