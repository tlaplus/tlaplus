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
package tlc2.module;

import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.IntervalValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueHarness;

/**
 * Checks {@link TLC#CombineFcn} for functions with interval domains.
 * JBMC bounds each domain's cardinality to three elements; interval endpoints remain unrestricted.
 * The functions map their domains to disjoint ranges, so an off-by-one into either values array changes the result.
 */
public final class TLCHarness extends ValueHarness {
	private static final int MAX_SMALL_SIZE = 3;
	private static final int BASE = 0;
	private static final int OTHER_BASE = MAX_SMALL_SIZE;

	// JBMC/CBMC treats all parameters as unconstrained nondeterministic inputs.
	// TLA+: checks f @@ g for DOMAIN f = low..high and DOMAIN g = otherLow..otherHigh.
	public static void verify(final int test, final int low, final int high, final int otherLow, final int otherHigh) {
		switch (test) {
		case 0:
			// Check that combining with an empty function on the right preserves every pair of f.
			verifyLeftInterval(low, high, otherLow, otherHigh);
			break;
		case 1:
			// Check that combining with an empty function on the left preserves every pair of g.
			verifyRightInterval(low, high, otherLow, otherHigh);
			break;
		case 2:
			// Check that f takes precedence on a shared key, including singletons at Integer.MIN_VALUE and
			// Integer.MAX_VALUE.
			verifyBoundarySingletons(low, high, otherLow, otherHigh);
			break;
		default:
			// SKIP: This selector value does not identify a property to check.
			return;
		}
	}

	// TLA+: f @@ g = f, DOMAIN g = {}.
	private static void verifyLeftInterval(final int low, final int high, final int otherLow, final int otherHigh) {
		final int size = ValueHarness.smallSize(low, high, MAX_SMALL_SIZE);
		final int otherSize = ValueHarness.smallSize(otherLow, otherHigh, MAX_SMALL_SIZE);
		if (size < 0 || otherSize != 0) {
			// SKIP: The left interval exceeds the cardinality bound, or the right interval is not empty.
			return;
		}
		verifyCombine(low, high, size, otherLow, otherHigh, otherSize);
	}

	// TLA+: f @@ g = g, DOMAIN f = {}.
	private static void verifyRightInterval(final int low, final int high, final int otherLow, final int otherHigh) {
		final int size = ValueHarness.smallSize(low, high, MAX_SMALL_SIZE);
		final int otherSize = ValueHarness.smallSize(otherLow, otherHigh, MAX_SMALL_SIZE);
		if (otherSize < 0 || size != 0) {
			// SKIP: The right interval exceeds the cardinality bound, or the left interval is not empty.
			return;
		}
		verifyCombine(low, high, size, otherLow, otherHigh, otherSize);
	}

	// TLA+: \A x \in DOMAIN f : (f @@ g)[x] = f[x], Cardinality(DOMAIN f) <= 1, Cardinality(DOMAIN g) <= 1.
	private static void verifyBoundarySingletons(final int low, final int high, final int otherLow,
			final int otherHigh) {
		final int size = ValueHarness.smallSize(low, high, MAX_SMALL_SIZE);
		final int otherSize = ValueHarness.smallSize(otherLow, otherHigh, MAX_SMALL_SIZE);
		if (size < 0 || size > 1 || otherSize < 0 || otherSize > 1) {
			// SKIP: Precedence is checked only for empty and singleton domains.
			return;
		}
		verifyCombine(low, high, size, otherLow, otherHigh, otherSize);
	}

	// TLA+: f @@ g = [x \in DOMAIN f \cup DOMAIN g |-> IF x \in DOMAIN f THEN f[x] ELSE g[x]].
	private static void verifyCombine(final int low, final int high, final int size, final int otherLow,
			final int otherHigh, final int otherSize) {
		final Value combined = TLC.CombineFcn(function(low, high, size, BASE),
				function(otherLow, otherHigh, otherSize, OTHER_BASE));
		assert combined instanceof FcnRcdValue : "Combining two functions must produce a function value.";
		final FcnRcdValue result = (FcnRcdValue) combined;
		// JBMC reports spurious element values for arrays whose length depends on the inputs, so use a fixed length.
		final long[] keys = new long[2 * MAX_SMALL_SIZE];
		final int[] values = new int[2 * MAX_SMALL_SIZE];
		final int length = specCombine(low, size, otherLow, otherSize, keys, values);
		assert result.domain != null : "Combining functions must produce an explicit domain.";
		assert result.domain.length == length : "The combined domain must contain each key of either domain once.";
		assert result.values.length == length : "The combined function must store one value per domain key.";
		for (int i = 0; i < length; i++) {
			assert isKey(result.domain[i], keys[i])
					: "The combined domain must list the keys of f, then the keys of g outside DOMAIN f.";
			assert ValueHarness.isInt(result.values[i], values[i])
					: "Each key must map to its value in f, or else to its value in g.";
		}
	}

	// Specification of CombineFcn(): the pairs of f in domain order, followed by the pairs of g whose keys are
	// outside DOMAIN f. Keys are computed with long arithmetic so a wrapped low + i cannot match.
	// Returns the number of pairs written to keys and values.
	private static int specCombine(final int low, final int size, final int otherLow, final int otherSize,
			final long[] keys, final int[] values) {
		int length = 0;
		for (int i = 0; i < size; i++) {
			keys[length] = (long) low + i;
			values[length] = BASE + i;
			length++;
		}
		for (int i = 0; i < otherSize; i++) {
			final long key = (long) otherLow + i;
			if (key < low || key >= (long) low + size) {
				keys[length] = key;
				values[length] = OTHER_BASE + i;
				length++;
			}
		}
		return length;
	}

	// Build [x \in low..high |-> base + x - low]. The caller checks that size is the interval's cardinality.
	private static FcnRcdValue function(final int low, final int high, final int size, final int base) {
		final Value[] values = new Value[size];
		for (int i = 0; i < size; i++) {
			values[i] = IntValue.gen(base + i);
		}
		return new FcnRcdValue(new IntervalValue(low, high), values);
	}

	// Compare against the mathematical key so a wrapped low + offset fails.
	private static boolean isKey(final Value value, final long expected) {
		return value instanceof IntValue && ((IntValue) value).val == expected;
	}
}
