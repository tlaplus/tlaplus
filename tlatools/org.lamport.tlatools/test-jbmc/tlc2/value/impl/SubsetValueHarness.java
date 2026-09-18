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
 * Checks the production SubsetValue implementation with production TLC values.
 * All primitive parameters are unconstrained JBMC inputs.
 */
public final class SubsetValueHarness {
	public static void verifySize(final int baseSize) {
		if (baseSize < 0 || baseSize > 3) {
			return;
		}
		final SubsetValue powerSet = new SubsetValue(base(baseSize));
		assert powerSet.size() == (1 << baseSize);
	}

	public static void verifyComparison(final int left, final int right) {
		final SubsetValue lhs = new SubsetValue(new IntervalValue(left, left));
		final SubsetValue rhs = new SubsetValue(new IntervalValue(right, right));
		final int expected = left < right ? -1 : left == right ? 0 : 1;
		assert lhs.compareTo(rhs) == expected && rhs.compareTo(lhs) == -expected;
	}

	public static void verifyEquality(final int left, final int right) {
		final SubsetValue lhs = new SubsetValue(new IntervalValue(left, left));
		final SubsetValue rhs = new SubsetValue(new IntervalValue(right, right));
		assert lhs.equals(rhs) == (left == right);
	}

	public static void verifyLifecycle(final int baseSize) {
		if (baseSize < 0 || baseSize > 3) {
			return;
		}
		final SetEnumValue base = base(baseSize);
		final SubsetValue powerSet = new SubsetValue(base);
		final boolean initial = powerSet.isFinite() && powerSet.isDefined()
				&& !powerSet.isNormalized() && powerSet.deepCopy() == powerSet;
		final boolean normalized = powerSet.normalize() == powerSet && base.isNormalized();
		powerSet.deepNormalize();
		assert initial && normalized && base.isNormalized();
	}

	public static void verifyExcept(final int replacement) {
		final SubsetValue powerSet = new SubsetValue(base(0));
		final Value value = IntValue.gen(replacement);
		final ValueExcept except = new ValueExcept(new Value[0], value);
		assert powerSet.takeExcept(except) == value
				&& powerSet.takeExcept(new ValueExcept[0]) == powerSet;
	}

	public static void verifySetRelations(final int baseSize, final int candidateSize) {
		if (baseSize < 0 || baseSize > 3 || candidateSize < 0 || candidateSize > 3) {
			return;
		}
		final SubsetValue powerSet = new SubsetValue(base(baseSize));
		final SetEnumValue candidate = base(candidateSize);
		final SubsetValue candidatePowerSet = new SubsetValue(candidate);
		assert powerSet.member(candidate) == (candidateSize <= baseSize)
				&& (powerSet.isSubsetEq(candidatePowerSet) == BoolValue.ValTrue)
						== (baseSize <= candidateSize);
	}

	private static SetEnumValue base(final int size) {
		final Value[] values = new Value[size];
		for (int i = 0; i < size; i++) {
			values[i] = IntValue.gen(i);
		}
		return new SetEnumValue(values, true);
	}
}
