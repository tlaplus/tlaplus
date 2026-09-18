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

/**
 * JBMC checks these assertions against the production {@link FcnRcdValue}
 * bytecode. All integer parameters are unconstrained JBMC inputs; in
 * particular, the harness does not seed known overflow boundary values.
 */
public final class FcnRcdValueHarness {

	public static void verify(final int test, final int first, final int second, final int argument) {
		switch (test) {
		case 0:
			verifyIntervalComparison(first, second);
			break;
		case 1:
			verifyExplicitToIntervalComparison(first, second);
			break;
		case 2:
			verifyIntervalToExplicitComparison(first, second);
			break;
		case 3:
			verifyEquality(first, second);
			break;
		case 4:
			verifySelection(first, second, argument);
			break;
		case 5:
			verifyExcept(first, second, argument);
			break;
		default:
			break;
		}
	}

	private static void verifyIntervalComparison(final int first, final int second) {
		if (first == second) {
			return;
		}
		final FcnRcdValue left = interval(first, first, 0);
		final FcnRcdValue right = interval(second, second, 0);
		assert sameOrder(left.compareTo(right), first, second);
	}

	private static void verifyExplicitToIntervalComparison(final int first, final int second) {
		if (first == second) {
			return;
		}
		final FcnRcdValue explicit = explicit(new int[] { first }, new int[] { 0 }, true);
		final FcnRcdValue interval = interval(second, second, 0);
		assert sameOrder(explicit.compareTo(interval), first, second);
	}

	private static void verifyIntervalToExplicitComparison(final int first, final int second) {
		if (first == second) {
			return;
		}
		final FcnRcdValue interval = interval(first, first, 0);
		final FcnRcdValue explicit = explicit(new int[] { second }, new int[] { 0 }, true);
		assert sameOrder(interval.compareTo(explicit), first, second);
	}

	private static void verifyEquality(final int first, final int second) {
		final FcnRcdValue explicit = explicit(
				new int[] { first, second }, new int[] { 0, 1 }, true);
		final FcnRcdValue interval = interval(first, first, new int[] { 0, 1 });
		assert explicit.equals(interval) == ((long) second == (long) first + 1L);
	}

	private static void verifySelection(final int low, final int high, final int argument) {
		if (argument < low || argument > high
				|| (long) argument - low <= Integer.MAX_VALUE) {
			return;
		}
		final FcnRcdValue function = interval(low, high, new int[] { 0 });
		assert function.select(IntValue.gen(argument)) == null;
	}

	private static void verifyExcept(final int low, final int high, final int argument) {
		if (argument < low || argument > high
				|| (long) argument - low <= Integer.MAX_VALUE) {
			return;
		}
		final FcnRcdValue function = interval(low, high, new int[] { 0 });
		final ValueExcept except = new ValueExcept(
				new Value[] { IntValue.gen(argument) }, IntValue.gen(1));
		assert function.takeExcept(except) == function;
	}

	private static boolean sameOrder(final int comparison, final int first, final int second) {
		return first < second ? comparison < 0 : comparison > 0;
	}

	private static FcnRcdValue interval(final int low, final int high, final int value) {
		return interval(low, high, new int[] { value });
	}

	private static FcnRcdValue interval(final int low, final int high, final int[] values) {
		return new FcnRcdValue(new IntervalValue(low, high), ints(values));
	}

	private static FcnRcdValue explicit(final int[] domain, final int[] values, final boolean normalized) {
		return new FcnRcdValue(ints(domain), ints(values), normalized);
	}

	private static Value[] ints(final int[] values) {
		final Value[] result = new Value[values.length];
		for (int i = 0; i < values.length; i++) {
			result[i] = IntValue.gen(values[i]);
		}
		return result;
	}
}
