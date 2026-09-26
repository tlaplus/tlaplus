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
		case 5:
			verifySize(low, high);
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
		switch (size) {
		case 0:
			verifyEmptyEnumeration(elements);
			break;
		case 1:
			verifySingletonEnumeration(elements, low);
			break;
		case 2:
			verifyPairEnumeration(elements, low);
			break;
		case MAX_SMALL_SIZE:
			verifyTripleEnumeration(elements, low);
			break;
		default:
			assert false : "Every interval within the cardinality bound must have an enumeration check.";
		}
	}

	// TLA+ enumeration sequence: <<>> for an empty interval.
	private static void verifyEmptyEnumeration(final ValueEnumeration elements) {
		assert elements.nextElement() == null : "An empty interval must have no elements to enumerate.";
		elements.reset();
		assert elements.nextElement() == null : "An empty interval must remain exhausted after reset.";
	}

	// TLA+ enumeration sequence: <<low>> for low..low.
	private static void verifySingletonEnumeration(final ValueEnumeration elements, final int low) {
		assert ValueHarness.isInt(elements.nextElement(), low) : "A singleton interval must enumerate its lower bound.";
		assert elements.nextElement() == null : "A singleton interval must be exhausted after one element.";
		elements.reset();
		assert ValueHarness.isInt(elements.nextElement(), low)
				: "Reset must restart a singleton interval at its lower bound.";
	}

	// TLA+ enumeration sequence: <<low, low + 1>> for low..(low + 1).
	private static void verifyPairEnumeration(final ValueEnumeration elements, final int low) {
		assert ValueHarness.isInt(elements.nextElement(), low) : "A two-element interval must start at its lower bound.";
		assert ValueHarness.isInt(elements.nextElement(), low + 1)
				: "A two-element interval must enumerate the next consecutive integer.";
		assert elements.nextElement() == null : "A two-element interval must be exhausted after two elements.";
		elements.reset();
		assert ValueHarness.isInt(elements.nextElement(), low)
				: "Reset must restart a two-element interval at its lower bound.";
	}

	// TLA+ enumeration sequence: <<low, low + 1, low + 2>> for low..(low + 2).
	private static void verifyTripleEnumeration(final ValueEnumeration elements, final int low) {
		assert ValueHarness.isInt(elements.nextElement(), low) : "A three-element interval must start at its lower bound.";
		assert ValueHarness.isInt(elements.nextElement(), low + 1)
				: "The second element of a three-element interval must follow its lower bound.";
		assert ValueHarness.isInt(elements.nextElement(), low + 2)
				: "The third element of a three-element interval must follow its second element.";
		assert elements.nextElement() == null : "A three-element interval must be exhausted after three elements.";
		elements.reset();
		assert ValueHarness.isInt(elements.nextElement(), low)
				: "Reset must restart a three-element interval at its lower bound.";
	}

	// TLA+: (low..high) \ {} = low..high.
	private static void verifyDiff(final int low, final int high) {
		final int size = ValueHarness.smallSize(low, high, MAX_SMALL_SIZE);
		if (size < 0) {
			// SKIP: The interval exceeds the cardinality bound for these checks.
			return;
		}
		verifyInterval(new IntervalValue(low, high).diff(SetEnumValue.EmptySet), low, size);
	}

	// TLA+: (low..high) \cap (low..high) = low..high.
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

	// TLA+: Cardinality(low..high), or a TLC error if it exceeds Integer.MAX_VALUE.
	// Check that size() agrees with its specification for every pair of endpoints.
	private static void verifySize(final int low, final int high) {
		final boolean specFails = specSize(low, high) < 0;
		boolean sizeFails = false;
		int size = -1;
		try {
			size = new IntervalValue(low, high).size();
		} catch (final RuntimeException e) {
			sizeFails = true;
		}
		assert sizeFails == specFails : "size() must fail exactly when the specification overflows.";
		assert sizeFails || size == specSize(low, high) : "size() must equal the specified cardinality.";
	}

	// Specification of size(): Math.addExact(Math.subtractExact(high, low), 1)
	// with the JDK's overflow checks inlined, because JBMC has no models for the
	// exact-arithmetic methods. Returns -1 where either method would throw
	// ArithmeticException.
	private static int specSize(final int low, final int high) {
		if (high < low) {
			return 0;
		}
		final int diff = high - low;
		if (((high ^ low) & (high ^ diff)) < 0) {
			return -1;
		}
		final int size = diff + 1;
		if (((diff ^ size) & (1 ^ size)) < 0) {
			return -1;
		}
		return size;
	}

	private static void verifyInterval(final Value result, final int low, final int size) {
		assert result instanceof SetEnumValue : "The interval result must be an enumerated set.";
		final ValueVec elements = ((SetEnumValue) result).elems;
		assert elements.size() == size : "The enumerated set must preserve the interval's cardinality.";
		if (size >= 1) {
			assert ValueHarness.isInt(elements.elementAt(0), low) : "The enumerated set must start at the lower bound.";
		}
		if (size >= 2) {
			assert ValueHarness.isInt(elements.elementAt(1), low + 1)
					: "The second element of the enumerated set must follow the lower bound.";
		}
		if (size >= 3) {
			assert ValueHarness.isInt(elements.elementAt(2), low + 2)
					: "The third element of the enumerated set must follow its second element.";
		}
	}
}
