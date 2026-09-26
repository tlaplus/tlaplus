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
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.value.impl;

import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.OpDeclNode;
import tlc2.tool.EvalControl;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateMut;
import tlc2.util.Context;

/**
 * Checks functions of the form [x \in low..high |-> e] with integer values.
 * JBMC bounds the values array; interval endpoints remain unrestricted.
 * Each function caches its values as an interval-backed function, so application needs no Tool to evaluate e.
 */
public final class FcnLambdaValueHarness extends ValueHarness {
	// JBMC/CBMC treats all parameters as unconstrained nondeterministic inputs.
	// TLA+: checks the identities below for functions within JBMC's input array bound.
	public static void verify(final int test, final int low, final int high, final int[] values) {
		if (values == null) {
			// SKIP: A null array cannot supply the function's values.
			return;
		}
		switch (test) {
		case 0:
			// Check that conversion recognizes sequence domains and preserves their elements.
			verifyToTuple(low, high, values);
			break;
		default:
			// SKIP: This selector value does not identify a property to check.
			return;
		}
	}

	// Convert exactly the interval-domain functions that are sequences, preserving their values.
	// TLA+: f \in Seq(Int) <=> DOMAIN f = 1..Cardinality(DOMAIN f), DOMAIN f = low..high.
	private static void verifyToTuple(final int low, final int high, final int[] values) {
		if (ValueHarness.cardinality(low, high) != values.length) {
			// SKIP: Sequence conversion is checked only for functions with one value per domain key.
			return;
		}
		final Value converted = function(low, high, values).toTuple();
		if (values.length != 0 && low != 1) {
			assert converted == null : "Nonempty sequences must start at index 1; other nonempty domains cannot convert.";
			return;
		}
		assert converted instanceof TupleValue : "A domain of 1..n, including any empty interval, must convert to a tuple.";
		final Value[] elements = ((TupleValue) converted).elems;
		assert elements.length == values.length : "Conversion must preserve the number of sequence elements.";
		for (int i = 0; i < values.length; i++) {
			assert ValueHarness.isInt(elements[i], values[i])
					: "Each sequence position must retain the value stored at its corresponding key.";
		}
	}

	// Build [x \in low..high |-> values[x - low + 1]]. The caller checks that values has one entry per key.
	private static FcnLambdaValue function(final int low, final int high, final int[] values) {
		TLCStateMut.setVariables(new OpDeclNode[0]);
		final FcnParams params = new FcnParams(new FormalParamNode[][] { new FormalParamNode[1] },
				new boolean[] { false }, new Value[] { new IntervalValue(low, high) });
		final FcnLambdaValue function = new FcnLambdaValue(params, null, null, Context.Empty, TLCState.Empty, null,
				EvalControl.Clear);
		final IntValue[] entries = new IntValue[values.length];
		for (int i = 0; i < values.length; i++) {
			entries[i] = IntValue.gen(values[i]);
		}
		function.fcnRcd = new FcnRcdValue(new IntervalValue(low, high), entries);
		return function;
	}
}
