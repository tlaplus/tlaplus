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

import java.lang.reflect.Proxy;

import org.openjdk.jcstress.annotations.Actor;
import org.openjdk.jcstress.annotations.Expect;
import org.openjdk.jcstress.annotations.JCStressTest;
import org.openjdk.jcstress.annotations.Outcome;
import org.openjdk.jcstress.annotations.State;
import org.openjdk.jcstress.infra.results.II_Result;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.SemanticNode;
import tlc2.tool.EvalControl;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStates;
import tlc2.util.Context;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.IntervalValue;
import tlc2.value.impl.SetPredValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueEnumeration;
import util.UniqueString;

/**
 * The set S == {x \in 1..4 : x % 2 = 0}. A worker that enumerates S while
 * another worker computes the size of S must see exactly 2 and 4.
 * <p>
 * SetPredValue#size replaces the plain field inVal with the filtered set and
 * then sets the volatile converted. SetPredValue#elements reads converted and,
 * if false, the Enumerator reads inVal without a happens-before edge to the
 * write of inVal. If the reader sees the filtered set, which it then filters
 * again, its contents must have been published, or the reader fails (-1) or
 * misses elements. The x86 memory model hides this; run on AArch64.
 * 
 * @see SetPredValueConvertedTest
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
@JCStressTest
@Outcome(id = "2, 6", expect = Expect.ACCEPTABLE, desc = "The reader enumerated 2 and 4.")
@Outcome(expect = Expect.FORBIDDEN, desc = "The reader enumerated the wrong elements " + Codes.LEGEND + ".")
@State
public class SetPredValueEnumeratorTest {

	private static final FormalParamNode X = new FormalParamNode(UniqueString.of("x"), 0, SyntaxTreeNode.nullSTN,
			null, null);

	/** Evaluates the predicate x % 2 = 0. */
	private static final ITool TOOL = (ITool) Proxy.newProxyInstance(ITool.class.getClassLoader(),
			new Class<?>[] { ITool.class }, (proxy, method, args) -> {
				if ("eval".equals(method.getName())) {
					return ((IntValue) ((Context) args[1]).lookup(X)).val % 2 == 0 ? BoolValue.ValTrue
							: BoolValue.ValFalse;
				}
				throw new UnsupportedOperationException(method.getName());
			});

	private static final TLCState STATE = TLCStates.createDummyState();

	private final SetPredValue set = new SetPredValue(X, new IntervalValue(1, 4), SemanticNode.nullSN, TOOL,
			Context.Empty, STATE, null, EvalControl.Clear);

	@Actor
	public void publisher(final II_Result r) {
		try {
			r.r1 = set.size();
		} catch (Throwable e) {
			r.r1 = Codes.of(e);
		}
	}

	/** Returns the sum of the elements, which is 2 + 4 = 6. */
	@Actor
	public void reader(final II_Result r) {
		try {
			final ValueEnumeration e = set.elements();
			int sum = 0;
			Value elem;
			while ((elem = e.nextElement()) != null) {
				sum += ((IntValue) elem).val;
			}
			r.r2 = sum;
		} catch (Throwable e) {
			r.r2 = Codes.of(e);
		}
	}
}
