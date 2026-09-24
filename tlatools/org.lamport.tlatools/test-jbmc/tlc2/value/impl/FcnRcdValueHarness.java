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
 * Checks functions with integer keys and values, and normalization with function keys.
 * JBMC bounds the input array lengths; integer values and interval endpoints remain unrestricted.
 * Explicit keys in the comparison cases must be sorted and distinct.
 * Construction reverses them and their values to exercise production normalization.
 *
 * Order(f) below is the sequence of its size, sorted keys, and corresponding values. LexCompare compares those
 * sequences; Compare denotes compareTo, and NoValue denotes Java null.
 */
public final class FcnRcdValueHarness extends ValueHarness {
	// JBMC/CBMC treats all parameters as unconstrained nondeterministic inputs.
	// TLA+: checks the identities below for functions within JBMC's input array bound.
	public static void verify(final int test, final boolean otherInterval, final int low, final int high,
			final int otherLow, final int otherHigh, final int[] keys, final int[] values, final int[] otherKeys,
			final int[] otherValues, final int key) {
		if (keys == null || values == null || otherKeys == null || otherValues == null) {
			// SKIP: Null arrays cannot supply the domains and values required by the checks.
			return;
		}
		switch (test) {
		case 0:
			// Exercise comparison and equality with an interval-backed left operand.
			verifyCompareToInterval(low, high, values, otherInterval, otherLow, otherHigh, otherKeys, otherValues);
			break;
		case 1:
			// Exercise comparison and equality with explicit keys that require normalization.
			verifyCompareToOther(keys, values, otherInterval, otherLow, otherHigh, otherKeys, otherValues);
			break;
		case 2:
			// Check lookup on well-formed interval functions with one stored value per key.
			verifySelect(low, high, key, values);
			break;
		case 3:
			// Check that lookup also handles interval keys without corresponding stored values.
			verifySelectBounds(low, high, key, values);
			break;
		case 4:
			// Check that conversion recognizes sequence domains and preserves their elements.
			verifyToTuple(low, high, values);
			break;
		case 5:
			// Check that overflow cannot cause false equality when FcnRcdValue's invariants are violated.
			verifyEqualsOverflow(low, keys, values);
			break;
		case 6:
			// Check that a one-key update preserves the domain and leaves the original function intact.
			// Use the otherwise unused endpoint as an independent replacement value.
			verifyTakeExcept(low, high, key, otherLow, values);
			break;
		case 7:
			// Exercise lookup on normalized explicit keys through both search strategies.
			verifySelectBinarySearch(keys, values, key);
			break;
		case 8:
			// Check that sorting integer keys preserves their associated values.
			verifyNormalize(keys, values);
			break;
		case 9:
			// Check that normalization also orders function-valued keys without changing their mappings.
			verifyNormalizeFunctionKeys(keys, otherKeys, values);
			break;
		default:
			// SKIP: This selector value does not identify a property to check.
			return;
		}
	}

	// Compare an interval domain against either kind of domain.
	// TLA+: Sign(Compare(f, g)) = LexCompare(Order(f), Order(g)), DOMAIN f = low..high.
	// In particular: f = g <=> DOMAIN f = DOMAIN g /\ \A x \in DOMAIN f : f[x] = g[x].
	private static void verifyCompareToInterval(final int low, final int high, final int[] values,
			final boolean otherInterval, final int otherLow, final int otherHigh, final int[] otherKeys,
			final int[] otherValues) {
		// Separate calls let JBMC see whether the other domain is an interval.
		if (otherInterval) {
			// Check ordering and equality when both functions use interval domains.
			verifyCompare(new IntervalValue(low, high), null, values, new IntervalValue(otherLow, otherHigh), null, otherValues);
			return;
		}
		// Check ordering and equality across interval and explicit-key representations.
		verifyCompare(new IntervalValue(low, high), null, values, null, otherKeys, otherValues);
	}

	// Compare explicit keys against either kind of domain.
	// TLA+: Sign(Compare(f, g)) = LexCompare(Order(f), Order(g)), DOMAIN f = {keys[i] : i \in DOMAIN keys}.
	// In particular: f = g <=> DOMAIN f = DOMAIN g /\ \A x \in DOMAIN f : f[x] = g[x].
	private static void verifyCompareToOther(final int[] keys, final int[] values, final boolean otherInterval,
			final int otherLow, final int otherHigh, final int[] otherKeys, final int[] otherValues) {
		if (otherInterval) {
			// Check ordering and equality with explicit keys on the left and an interval on the right.
			verifyCompare(null, keys, values, new IntervalValue(otherLow, otherHigh), null, otherValues);
			return;
		}
		// Check ordering and equality when both functions need their explicit keys normalized.
		verifyCompare(null, keys, values, null, otherKeys, otherValues);
	}

	// Check lookup when the interval and the values array have the same size.
	// TLA+: Select(f, key) = IF key \in DOMAIN f THEN f[key] ELSE NoValue, DOMAIN f = low..high.
	private static void verifySelect(final int low, final int high, final int key, final int[] values) {
		if (ValueHarness.cardinality(low, high) != values.length) {
			// SKIP: The input does not provide exactly one value for each domain key.
			return;
		}
		final FcnRcdValue function = function(new IntervalValue(low, high), null, values, values.length);
		final Value selected = function.select(IntValue.gen(key));
		if (low <= key && key <= high) {
			assert ValueHarness.isInt(selected, values[(int) ((long) key - low)])
					: "Domain members must yield their associated value.";
		} else {
			assert selected == null : "Keys outside the domain must yield no value.";
		}
	}

	// Also check intervals with more keys than the values array can hold.
	// TLA+: SelectStored(v, key) = IF key \in low..high /\ key-low+1 \in DOMAIN v
	//                            THEN v[key-low+1] ELSE NoValue.
	private static void verifySelectBounds(final int low, final int high, final int key, final int[] values) {
		final FcnRcdValue function = function(new IntervalValue(low, high), null, values, values.length);
		final Value selected = function.select(IntValue.gen(key));
		final long offset = (long) key - low;
		final boolean present = low <= key && key <= high && offset < values.length;
		if (present) {
			assert ValueHarness.isInt(selected, values[(int) offset])
					: "A domain key with a stored array entry must yield that entry's value.";
		} else {
			assert selected == null : "A key outside the domain or without a stored entry must yield no value.";
		}
	}

	// Convert exactly the interval-domain functions that are sequences, preserving their values.
	// TLA+: f \in Seq(Int) <=> DOMAIN f = 1..Cardinality(DOMAIN f), DOMAIN f = low..high.
	private static void verifyToTuple(final int low, final int high, final int[] values) {
		if (ValueHarness.cardinality(low, high) != values.length) {
			// SKIP: Sequence conversion is checked only for functions with one value per domain key.
			return;
		}
		final FcnRcdValue function = function(new IntervalValue(low, high), null, values, values.length);
		final Value converted = function.toTuple();
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

	// Check functions that violate FcnRcdValue's invariants: their stored values would require interval keys beyond
	// Integer.MAX_VALUE.
	// TLA+: \E i \in 1..Len(keys) : keys[i] # low + i - 1.
	private static void verifyEqualsOverflow(final int low, final int[] keys, final int[] values) {
		if (keys.length != values.length || values.length == 0 || (long) low + values.length - 1 <= Integer.MAX_VALUE) {
			// SKIP: The input lacks matching nonempty arrays or does not exercise integer-key overflow.
			return;
		}
		final FcnRcdValue interval = function(new IntervalValue(low, Integer.MAX_VALUE), null, values, values.length);
		final IntValue[] domain = new IntValue[keys.length];
		for (int i = 0; i < keys.length; i++) {
			domain[i] = IntValue.gen(keys[i]);
		}
		// Keep the supplied order, even if wrapped keys make the normalized flag incorrect.
		final FcnRcdValue explicit = new FcnRcdValue(domain, interval.values, true);
		assert !explicit.equals(interval)
				: "Explicit keys must not equal an interval function whose stored entries imply integer-key overflow.";
		assert !interval.equals(explicit)
				: "An interval function violating FcnRcdValue's invariants must also reject equality in the reverse direction.";
	}

	// Check one-key updates without changing the original function.
	// TLA+: [f EXCEPT ![key] = replacement], DOMAIN f = low..high.
	// Also allow intervals larger than the values array; missing entries must be ignored.
	private static void verifyTakeExcept(final int low, final int high, final int key, final int replacement,
			final int[] values) {
		final FcnRcdValue function = function(new IntervalValue(low, high), null, values, values.length);
		final ValueExcept except = new ValueExcept(new IntValue[] { IntValue.gen(key) }, IntValue.gen(replacement));
		final Value result = function.takeExcept(except);
		assert result instanceof FcnRcdValue : "Updating a function entry must produce a function value.";
		final FcnRcdValue updated = (FcnRcdValue) result;
		assert updated.intv != null : "An entry update must preserve the interval domain representation.";
		assert updated.intv.low == low : "An entry update must preserve the domain's lower bound.";
		assert updated.intv.high == high : "An entry update must preserve the domain's upper bound.";
		assert updated.values.length == values.length : "An entry update must preserve the number of stored values.";
		assert function.intv.low == low : "An entry update must not modify the original domain's lower bound.";
		assert function.intv.high == high : "An entry update must not modify the original domain's upper bound.";
		final long offset = (long) key - low;
		for (int i = 0; i < values.length; i++) {
			// Replace only a stored entry addressed by a domain key; all other entries stay unchanged.
			final int expected = low <= key && key <= high && offset == i ? replacement : values[i];
			assert ValueHarness.isInt(updated.values[i], expected)
					: "Only the stored entry addressed by the update may change to the replacement value.";
			assert ValueHarness.isInt(function.values[i], values[i])
					: "An entry update must not modify the original function's values.";
		}
	}

	// Check lookup after production normalization, including keys absent from the domain.
	// TLA+: Select(f, key) = IF key \in DOMAIN f THEN f[key] ELSE NoValue.
	// The excluded property lookup leaves the search threshold unconstrained, so JBMC checks both binary and linear search
	// even with small arrays.
	private static void verifySelectBinarySearch(final int[] keys, final int[] values, final int key) {
		if (!validDomain(null, keys, values.length)) {
			// SKIP: Lookup requires distinct, sorted keys with exactly one value per key.
			return;
		}
		// As in verifyCompare, give JBMC a fixed array size for each path.
		for (int size = 0; size <= values.length; size++) {
			if (size != values.length) {
				// SKIP_ITERATION: This unrolled size does not match the symbolic array length.
				continue;
			}
			final FcnRcdValue function = function(null, keys, values, size);
			function.normalize();
			final Value selected = function.selectBinarySearch(IntValue.gen(key));
			for (int i = 0; i < size; i++) {
				if (keys[i] == key) {
					assert ValueHarness.isInt(selected, values[i])
							: "A present key must still select its original value after normalization.";
					return;
				}
			}
			assert selected == null : "No supplied key matched, so either search strategy must report no value.";
			return;
		}
		assert false : "No unrolled size matched the input length, so the lookup check was never reached.";
	}

	// Sort arbitrary distinct integer keys while keeping each key paired with its value.
	// TLA+: DOMAIN normalized = DOMAIN f /\ \A x \in DOMAIN f : normalized[x] = f[x].
	private static void verifyNormalize(final int[] keys, final int[] values) {
		if (keys.length != values.length) {
			// SKIP: The input cannot pair every domain key with exactly one value.
			return;
		}
		for (int i = 0; i < keys.length; i++) {
			for (int j = 0; j < i; j++) {
				if (keys[i] == keys[j]) {
					// SKIP: Duplicate domain keys are outside the inputs supported by normalization.
					return;
				}
			}
		}
		for (int size = 0; size <= values.length; size++) {
			if (size != values.length) {
				// SKIP_ITERATION: This unrolled size does not match the symbolic array length.
				continue;
			}
			final FcnRcdValue function = function(null, keys, values, size);
			final Value normalized = function.normalize();
			assert normalized == function : "Normalization must return the same function.";
			assert function.isNormalized() : "Normalization must set the normalized flag.";
			assert function.domain.length == size : "Normalization must preserve the number of domain keys.";
			assert function.values.length == size : "Normalization must preserve the number of stored values.";
			for (int i = 0; i < size; i++) {
				// Counting smaller keys gives the expected position without sorting them.
				int position = 0;
				for (int j = 0; j < size; j++) {
					if (keys[j] < keys[i]) {
						// Each smaller key occupies one position before this key in the normalized domain.
						position++;
					}
				}
				assert ValueHarness.isInt(function.domain[position], keys[i])
						: "Sorting must place each key at its expected position.";
				assert ValueHarness.isInt(function.values[position], values[i])
						: "Sorting must keep each key paired with its original value.";
			}
			return;
		}
		assert false : "No unrolled size matched the input length, so the normalization check was never reached.";
	}

	// Each key is the singleton function [x \in keys[i]..keys[i] |-> keyValues[i]].
	// TLA+: DOMAIN normalized = DOMAIN f /\ \A k \in DOMAIN f : normalized[k] = f[k].
	private static void verifyNormalizeFunctionKeys(final int[] keys, final int[] keyValues, final int[] values) {
		if (keys.length != values.length || keyValues.length != values.length) {
			// SKIP: The arrays cannot supply one singleton-function key and one value per outer entry.
			return;
		}
		for (int i = 0; i < keys.length; i++) {
			for (int j = 0; j < i; j++) {
				if (keys[i] == keys[j] && keyValues[i] == keyValues[j]) {
					// SKIP: Equal singleton domains and values make duplicate function keys.
					return;
				}
			}
		}
		// As in verifyCompare, give JBMC a fixed array size for each path.
		for (int size = 0; size <= values.length; size++) {
			if (size != values.length) {
				// SKIP_ITERATION: This unrolled size does not match the symbolic array length.
				continue;
			}
			final FcnRcdValue[] domain = new FcnRcdValue[size];
			final IntValue[] entries = new IntValue[size];
			for (int i = 0; i < size; i++) {
				domain[i] = function(new IntervalValue(keys[i], keys[i]), null, new int[] { keyValues[i] }, 1);
				entries[i] = IntValue.gen(values[i]);
			}
			final FcnRcdValue function = new FcnRcdValue(domain, entries, false);
			final Value normalized = function.normalize();
			assert normalized == function : "Normalization with function-valued keys must return the same function.";
			assert function.isNormalized() : "Normalization with function-valued keys must set the normalized flag.";
			for (int i = 0; i < size; i++) {
				// Order singleton functions by their integer domain, then their value.
				int position = 0;
				for (int j = 0; j < size; j++) {
					if (keys[j] < keys[i] || (keys[j] == keys[i] && keyValues[j] < keyValues[i])) {
						// Count singleton functions that precede this key to determine its expected position.
						position++;
					}
				}
				final FcnRcdValue normalizedKey = domain[position];
				assert normalizedKey != null : "Sorting must retain each singleton-function key.";
				assert normalizedKey.intv != null : "Sorting must preserve each key's interval domain representation.";
				assert normalizedKey.intv.low == keys[i] : "Sorting must place each key's lower bound at its expected position.";
				assert normalizedKey.intv.high == keys[i] : "Sorting must place each key's upper bound at its expected position.";
				assert normalizedKey.values.length == 1 : "Sorting must preserve each key's singleton structure.";
				assert ValueHarness.isInt(normalizedKey.values[0], keyValues[i])
						: "Sorting must preserve the value within each singleton-function key.";
				assert ValueHarness.isInt(function.values[position], values[i])
						: "Sorting must keep each function-valued key paired with its original outer value.";
			}
			return;
		}
		assert false : "No unrolled size matched the input length, so the function-key check was never reached.";
	}

	// Check ordering and equality against the sorted integer keys and their values.
	private static void verifyCompare(final IntervalValue interval, final int[] keys, final int[] values,
			final IntervalValue otherInterval, final int[] otherKeys, final int[] otherValues) {
		if (!validDomain(interval, keys, values.length) || !validDomain(otherInterval, otherKeys, otherValues.length)) {
			// SKIP: Comparison requires valid domains with exactly one stored value per key.
			return;
		}
		// JBMC unrolls these counters to constants. Only the actual lengths enter the comparison, giving the constructed
		// arrays fixed sizes without listing cases.
		for (int size = 0; size <= values.length; size++) {
			if (size != values.length) {
				continue;
			}
			for (int otherSize = 0; otherSize <= otherValues.length; otherSize++) {
				if (otherSize == otherValues.length) {
					final int[] domain = interval == null ? keys : intervalKeys(interval.low, size);
					final int[] otherDomain = otherInterval == null ? otherKeys : intervalKeys(otherInterval.low, otherSize);
					final int expected = specOrder(domain, values, otherDomain, otherValues);
					final FcnRcdValue left = function(interval, domain, values, size);
					final FcnRcdValue right = function(otherInterval, otherDomain, otherValues, otherSize);
					assert sign(left.compareTo(right)) == expected
							: "Function comparison must agree with the expected lexicographic order.";
					assert left.equals(right) == (expected == 0) : "Function equality must agree with the expected order.";
					assert right.equals(left) == (expected == 0)
							: "Function equality in the reverse direction must agree with the expected order.";
					return;
				}
			}
		}
		assert false : "No unrolled sizes matched the input lengths, so the comparison checks were never reached.";
	}

	// Require one key per value. Explicit keys must be distinct and in increasing order.
	private static boolean validDomain(final IntervalValue interval, final int[] keys, final int size) {
		if (interval != null) {
			return ValueHarness.cardinality(interval.low, interval.high) == size;
		}
		if (keys.length != size) {
			return false;
		}
		for (int i = 1; i < size; i++) {
			if (keys[i - 1] >= keys[i]) {
				return false;
			}
		}
		return true;
	}

	// List the interval's keys independently of TLC's enumeration. The caller checks its size first.
	private static int[] intervalKeys(final int low, final int size) {
		final int[] keys = new int[size];
		for (int i = 0; i < size; i++) {
			keys[i] = (int) ((long) low + i);
		}
		return keys;
	}

	// Build a production value. Reverse explicit keys and values to exercise normalization.
	private static FcnRcdValue function(final IntervalValue interval, final int[] keys, final int[] values,
			final int size) {
		final IntValue[] entries = new IntValue[size];
		if (interval != null) {
			for (int i = 0; i < size; i++) {
				entries[i] = IntValue.gen(values[i]);
			}
			return new FcnRcdValue(interval, entries);
		}
		if (size == 0) {
			return (FcnRcdValue) FcnRcdValue.EmptyFcn;
		}
		final IntValue[] domain = new IntValue[size];
		for (int i = 0; i < size; i++) {
			final int j = size - 1 - i;
			domain[i] = IntValue.gen(keys[j]);
			entries[i] = IntValue.gen(values[j]);
		}
		return new FcnRcdValue(domain, entries, false);
	}

	// Specification of compareTo(): compare sizes, then sorted keys, then corresponding values, using only integer
	// comparisons.
	private static int specOrder(final int[] keys, final int[] values, final int[] otherKeys, final int[] otherValues) {
		if (values.length != otherValues.length) {
			return values.length < otherValues.length ? -1 : 1;
		}
		for (int i = 0; i < keys.length; i++) {
			if (keys[i] != otherKeys[i]) {
				return keys[i] < otherKeys[i] ? -1 : 1;
			}
		}
		for (int i = 0; i < values.length; i++) {
			if (values[i] != otherValues[i]) {
				return values[i] < otherValues[i] ? -1 : 1;
			}
		}
		return 0;
	}

	// Reduce a comparison result to -1, 0, or 1.
	private static int sign(final int value) {
		return value < 0 ? -1 : value > 0 ? 1 : 0;
	}
}
