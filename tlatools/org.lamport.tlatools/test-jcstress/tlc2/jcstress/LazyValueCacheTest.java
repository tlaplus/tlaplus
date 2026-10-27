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
package tlc2.jcstress;

import static tlc2.value.impl.ValueFixtures.sortedSet;

import org.openjdk.jcstress.annotations.Actor;
import org.openjdk.jcstress.annotations.Expect;
import org.openjdk.jcstress.annotations.JCStressTest;
import org.openjdk.jcstress.annotations.Outcome;
import org.openjdk.jcstress.annotations.State;
import org.openjdk.jcstress.infra.results.II_Result;

import tla2sany.semantic.SemanticNode;
import tlc2.tool.EvalControl;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStates;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.LookupTool;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.impl.LazyValue;
import tlc2.value.impl.SetEnumValue;
import util.UniqueString;

/**
 * The lazy value of the expression v0, which two workers evaluate in the state
 * v0 = {1, 2, 3}, where the publisher creates its own {1, 2, 3}. If
 * LazyValue#getValue caches the value in val without a lock or volatile, the
 * reader may see the cache but, because SetEnumValue#elems isn't final, elems
 * as null (-1) or as an empty ValueVec. If it caches the value before the copy
 * of the state, the reader may see that copy without its values.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/439
 */
@JCStressTest
@Outcome(id = "3, 3", expect = Expect.ACCEPTABLE, desc = "Both workers see three elements.")
@Outcome(expect = Expect.FORBIDDEN, desc = "A worker saw the cache without its elements " + Codes.LEGEND + ".")
@State
public class LazyValueCacheTest {

	private static final UniqueString V0 = UniqueString.of("v0");

	private static final Tool TOOL = LookupTool.create(V0);

	private static final TLCState STATE = TLCStates.createDummyState().bind(V0, sortedSet(1, 2, 3));

	private final LazyValue lazy = new LazyValue(SemanticNode.nullSN, Context.Empty, true,
			CostModel.DO_NOT_RECORD);

	@Actor
	public void publisher(final II_Result r) {
		r.r1 = Codes.catching(() -> {
			final TLCState s = STATE.copy().bind(V0, sortedSet(1, 2, 3));
			return ((SetEnumValue) lazy.getValue(TOOL, s, null, EvalControl.Clear)).elems.size();
		});
	}

	@Actor
	public void reader(final II_Result r) {
		r.r2 = Codes.catching(
				() -> ((SetEnumValue) lazy.getValue(TOOL, STATE, null, EvalControl.Clear)).elems.size());
	}
}
