/*******************************************************************************
 * Copyright (c) 2022 Microsoft Research. All rights reserved. 
 * Copyright (c) 2023, Oracle and/or its affiliates.
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
package tlc2.value.impl;

import java.util.function.Supplier;

import tla2sany.semantic.SemanticNode;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;

public class LazySupplierValue extends LazyValue {

	private final Supplier<Value> s;

	public LazySupplierValue(SemanticNode sn, Supplier<Value> s) {
		super(sn, Context.Empty, CostModel.DO_NOT_RECORD);
		this.s = s;
	}

	@Override
	public Value getValue(Tool tool, TLCState s0, TLCState s1, int control) {
		// TODO: is it OK to ignore the args here?  What are the semantics of this particular value?
		return (Value) s.get();
	}
}
