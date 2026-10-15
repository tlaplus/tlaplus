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

import java.lang.reflect.Proxy;

import org.jetbrains.lincheck.datastructures.Operation;
import org.junit.Test;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.SemanticNode;
import tlc2.tool.EvalControl;
import tlc2.tool.ITool;
import tlc2.tool.TLCStates;
import tlc2.util.Context;
import util.UniqueString;

/**
 * The set S == {x \in {4, 1, 2, 3} : x % 2 = 0}, which TLC has not yet
 * enumerated. A worker that enumerates S while another worker fingerprints S
 * must still get 4 and 2, in either order, and in the order 2, 4 if it
 * normalizes S first. Fingerprinting replaces the set {4, 1, 2, 3} in S with
 * the enumeration of S. SetPredValue#elements and SetPredValue#normalize read
 * the set that S holds without converting S, so they may read either set.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class SetPredValueElementsTest extends ValueLincheckTestCase {

	private static final FormalParamNode X = new FormalParamNode(UniqueString.of("x"), 0, SyntaxTreeNode.nullSTN,
			null, null);

	/** Evaluates the predicate x % 2 = 0. */
	private static final ITool EVEN = (ITool) Proxy.newProxyInstance(ITool.class.getClassLoader(),
			new Class<?>[] { ITool.class }, (proxy, method, args) -> {
				if ("eval".equals(method.getName())) {
					return ((IntValue) ((Context) args[1]).lookup(X)).val % 2 == 0 ? BoolValue.ValTrue
							: BoolValue.ValFalse;
				}
				throw new UnsupportedOperationException(method.getName());
			});

	private final SetPredValue set;

	public SetPredValueElementsTest() {
		this(new SetPredValue(X,
				new SetEnumValue(new Value[] { IntValue.gen(4), IntValue.gen(1), IntValue.gen(2), IntValue.gen(3) },
						false),
				SemanticNode.nullSN, EVEN, Context.Empty, TLCStates.createDummyState(), null, EvalControl.Clear));
	}

	private SetPredValueElementsTest(final SetPredValue set) {
		super(set);
		this.set = set;
	}

	@Operation
	public String elements() {
		final StringBuilder sb = new StringBuilder();
		final ValueEnumeration elements = set.elements();
		Value elem;
		while ((elem = elements.nextElement()) != null) {
			sb.append(elem).append(' ');
		}
		return sb.toString();
	}

	@Operation
	public String normalizeAndElements() {
		set.normalize();
		return elements();
	}

	@Test
	public void fingerPrintAndElements() {
		modelCheckingParallel("fingerPrint", "elements");
	}

	@Test
	public void fingerPrintAndNormalizeAndElements() {
		modelCheckingParallel("fingerPrint", "normalizeAndElements");
	}
}
