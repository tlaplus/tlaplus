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
import java.util.function.Function;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.SemanticNode;
import tlc2.tool.EvalControl;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStates;
import tlc2.util.Context;
import util.UniqueString;

/**
 * Values that the concurrency tests in test-lincheck and test-jcstress share.
 * A tool here stands in for TLC's evaluation of the body of a value with the
 * bound identifier x.
 */
public final class ValueFixtures {

	public static final FormalParamNode X = new FormalParamNode(UniqueString.of("x"), 0, SyntaxTreeNode.nullSTN,
			null, null);

	/**
	 * A tool that evaluates every expression to x % 2 = 0, and supports nothing
	 * else.
	 */
	public static final ITool X_IS_EVEN = evaluating(
			c -> ((IntValue) c.lookup(X)).val % 2 == 0 ? BoolValue.ValTrue : BoolValue.ValFalse);

	private static final ITool SEVEN = evaluatingTo(IntValue.gen(7));

	private static final TLCState STATE = TLCStates.createDummyState();

	private ValueFixtures() {
	}

	/**
	 * The given integers.
	 */
	public static Value[] ints(final int... ns) {
		final Value[] vals = new Value[ns.length];
		for (int i = 0; i < ns.length; i++) {
			vals[i] = IntValue.gen(ns[i]);
		}
		return vals;
	}

	/**
	 * The set of the given integers, which must be in ascending order.
	 */
	public static SetEnumValue sortedSet(final int... elems) {
		return new SetEnumValue(ints(elems), true);
	}

	/**
	 * The sum of the integers that the enumeration returns.
	 */
	public static int sum(final ValueEnumeration elements) {
		int sum = 0;
		Value elem;
		while ((elem = elements.nextElement()) != null) {
			sum += ((IntValue) elem).val;
		}
		return sum;
	}

	/**
	 * A tool that evaluates every expression in a context to what eval maps the
	 * context to, and supports nothing else.
	 */
	public static ITool evaluating(final Function<Context, Value> eval) {
		return (ITool) Proxy.newProxyInstance(ITool.class.getClassLoader(), new Class<?>[] { ITool.class },
				(proxy, method, args) -> {
					if ("eval".equals(method.getName())) {
						return eval.apply(args.length > 1 && args[1] instanceof Context ? (Context) args[1]
								: Context.Empty);
					}
					throw new UnsupportedOperationException(method.getName());
				});
	}

	/**
	 * A tool that evaluates every expression to the given value, and supports
	 * nothing else.
	 */
	public static ITool evaluatingTo(final Value value) {
		return evaluating(c -> value);
	}

	/**
	 * The set {x \in set : P}, for the predicate P that tool evaluates.
	 */
	public static SetPredValue setPred(final Value set, final ITool tool) {
		return new SetPredValue(X, set, SemanticNode.nullSN, tool, Context.Empty, STATE, null, EvalControl.Clear);
	}

	/**
	 * The function [x \in 1..3 |-> 7], which TLC has not yet converted to a
	 * FcnRcdValue.
	 */
	public static FcnLambdaValue sevens() {
		return new FcnLambdaValue(
				new FcnParams(new FormalParamNode[][] { { X } }, new boolean[] { false },
						new Value[] { new IntervalValue(1, 3) }),
				SemanticNode.nullSN, SEVEN, Context.Empty, STATE, null, EvalControl.Clear);
	}

	/**
	 * The function [[x \in 1..3 |-> 7] EXCEPT ![2] = 99].
	 */
	public static FcnLambdaValue sevensExcept2() {
		return (FcnLambdaValue) sevens().takeExcept(new ValueExcept(ints(2), IntValue.gen(99)));
	}
}
