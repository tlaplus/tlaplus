/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
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

import org.jetbrains.lincheck.datastructures.Operation;
import org.junit.Test;

import tla2sany.semantic.SemanticNode;
import tlc2.tool.EvalControl;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStates;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.LookupTool;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import util.UniqueString;

/**
 * The lazy value of the expression v0, which has cached its value 1 in the
 * state v0 = 1. A worker that evaluates it in v0 = 1 while another worker
 * evaluates it in v0 = 2 must still get 1. If LazyValue#getValue caches the
 * value 2 and the state v0 = 2 in separate fields, without a lock, the first
 * worker may match the value 2 with the cached state v0 = 1.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class LazyValueCacheTest extends ValueLincheckTestCase {

	private static final UniqueString V0 = UniqueString.of("v0");

	private static final Tool TOOL = LookupTool.create(V0);

	private static final TLCState ONE = TLCStates.createDummyState().bind(V0, IntValue.gen(1));

	private static final TLCState TWO = TLCStates.createDummyState().bind(V0, IntValue.gen(2));

	private final LazyValue lazy = new LazyValue(SemanticNode.nullSN, Context.Empty, true, CostModel.DO_NOT_RECORD);

	public LazyValueCacheTest() {
		lazy.getValue(TOOL, ONE, null, EvalControl.Clear);
	}

	@Override
	protected Value value() {
		return lazy;
	}

	@Operation
	public int inOne() {
		return ((IntValue) lazy.getValue(TOOL, ONE, null, EvalControl.Clear)).val;
	}

	@Operation
	public int inTwo() {
		return ((IntValue) lazy.getValue(TOOL, TWO, null, EvalControl.Clear)).val;
	}

	@Test
	public void inTwoAndInOne() {
		modelCheckingParallel("inTwo", "inOne");
	}
}
