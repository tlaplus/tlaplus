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
 * Verifies bounded interval enumeration and set operations for every possible endpoint.
 */
public final class IntervalValueHarness extends ValueHarness {
	private static final int MAX_SMALL_SIZE = 3;

	// JBMC/CBMC treats all parameters as unconstrained nondeterministic inputs.
	// TLA+: checks the identities below for low..high with Cardinality(low..high) <= MAX_SMALL_SIZE.
	public static void verify(final int test, final int low, final int high, final long fp) {
		switch (test) {
		case 0:
			verifyEnumeration(low, high);
			break;
		case 1:
			verifyDiff(low, high);
			break;
		case 2:
			verifyCap(low, high);
			break;
		case 3:
			verifyCup(low, high);
			break;
		case 4:
			verifyFingerprint(low, high, fp);
			break;
		default:
			// SKIP: This selector value does not identify a property to check.
			return;
		}
	}

	// TLA+ enumeration sequence: [i \in 1..Cardinality(low..high) |-> low + i - 1].
	private static void verifyEnumeration(final int low, final int high) {
		final int size = ValueHarness.smallSize(low, high, MAX_SMALL_SIZE);
		if (size < 0) {
			// SKIP: The interval exceeds the cardinality bound for these checks.
			return;
		}
		final ValueEnumeration elements = new IntervalValue(low, high).elements();
		for (int i = 0; i < size; i++) {
			assert ValueHarness.isInt(elements.nextElement(), low + i)
					: "The enumeration must list the interval's elements in ascending order.";
		}
		assert elements.nextElement() == null : "The enumeration must be exhausted after the interval's last element.";
		elements.reset();
		final Value first = elements.nextElement();
		assert size == 0 ? first == null : ValueHarness.isInt(first, low)
				: "Reset must restart the enumeration at the interval's lower bound.";
	}

	// TLA+: (low..high) \ {} = low..high.
	// The empty set suffices: diff does not branch on its operand. It always walks
	// low..high by offset and only filters with val.member, which is false for {},
	// so every iteration runs and must keep its element.
	private static void verifyDiff(final int low, final int high) {
		final int size = ValueHarness.smallSize(low, high, MAX_SMALL_SIZE);
		if (size < 0) {
			// SKIP: The interval exceeds the cardinality bound for these checks.
			return;
		}
		verifyInterval(new IntervalValue(low, high).diff(SetEnumValue.EmptySet), low, size);
	}

	// TLA+: (low..high) \cap (low..high) = low..high.
	// The interval itself suffices: cap does not branch on its operand. It always
	// walks low..high by offset and only filters with val.member, which is true for
	// every element here, so every iteration runs and must keep its element.
	private static void verifyCap(final int low, final int high) {
		final int size = ValueHarness.smallSize(low, high, MAX_SMALL_SIZE);
		if (size < 0) {
			// SKIP: The interval exceeds the cardinality bound for these checks.
			return;
		}
		final IntervalValue interval = new IntervalValue(low, high);
		verifyInterval(interval.cap(interval), low, size);
	}

	// TLA+: (low..high) \cup {} = low..high.
	// The empty set suffices: for a Reducible operand, cup walks low..high by offset
	// regardless of the operand and then appends the operand's non-members, which
	// needs no endpoint arithmetic. Other operands yield a lazy SetCupValue, and an
	// empty interval returns the operand unchanged.
	private static void verifyCup(final int low, final int high) {
		final int size = ValueHarness.smallSize(low, high, MAX_SMALL_SIZE);
		if (size < 0) {
			// SKIP: The interval exceeds the cardinality bound for these checks.
			return;
		}
		verifyInterval(new IntervalValue(low, high).cup(SetEnumValue.EmptySet), low, size);
	}

	// TLA+: low..high = {low + i : i \in 0..(size - 1)}.
	// Check that these equal sets have identical fingerprints for the same seed.
	private static void verifyFingerprint(final int low, final int high, final long fp) {
		final int size = ValueHarness.smallSize(low, high, MAX_SMALL_SIZE);
		if (size < 0) {
			// SKIP: The interval exceeds the cardinality bound for these checks.
			return;
		}
		final IntervalValue interval = new IntervalValue(low, high);
		final Value set = interval.toSetEnum();
		// Validate the conversion independently before using it as the fingerprint reference.
		verifyInterval(set, low, size);
		assert interval.fingerPrint(fp) == set.fingerPrint(fp)
				: "An interval and its enumerated set must have identical fingerprints for the same seed.";
	}

	private static void verifyInterval(final Value result, final int low, final int size) {
		assert result instanceof SetEnumValue : "The interval result must be an enumerated set.";
		final ValueVec elements = ((SetEnumValue) result).elems;
		assert elements.size() == size : "The enumerated set must preserve the interval's cardinality.";
		for (int i = 0; i < size; i++) {
			assert ValueHarness.isInt(elements.elementAt(i), low + i)
					: "The enumerated set must list the interval's elements in ascending order.";
		}
	}
}
