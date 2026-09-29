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

public final class ValueVecHarness extends ValueHarness {

	// JBMC/CBMC treats all parameters as unconstrained nondeterministic inputs.
	// sort(true) yields {ints[i] : i \in DOMAIN ints} in strictly ascending order.
	public static void verifySortWithoutDuplicates(final int[] ints) {
		if (ints == null) {
			// SKIP: A null array cannot supply the vector's elements.
			return;
		}
		final ValueVec vec = vec(ints).sort(true);
		for (int i = 1; i < vec.size(); i++) {
			assert vec.elementAt(i - 1).compareTo(vec.elementAt(i)) < 0
					: "sort(true) must list the elements in strictly ascending order.";
		}
		for (int i = 0; i < ints.length; i++) {
			assert count(vec, ints[i]) == 1 : "sort(true) must keep every element exactly once.";
		}
		for (int i = 0; i < vec.size(); i++) {
			assert vec.elementAt(i) instanceof IntValue
					&& count(ints, ((IntValue) vec.elementAt(i)).val) > 0 : "sort(true) must not add elements.";
		}
	}

	// JBMC/CBMC treats all parameters as unconstrained nondeterministic inputs.
	// sort(false) yields a permutation of ints in ascending order.
	public static void verifySortWithDuplicates(final int[] ints) {
		if (ints == null) {
			// SKIP: A null array cannot supply the vector's elements.
			return;
		}
		final ValueVec vec = vec(ints).sort(false);
		for (int i = 1; i < vec.size(); i++) {
			assert vec.elementAt(i - 1).compareTo(vec.elementAt(i)) <= 0
					: "sort(false) must list the elements in ascending order.";
		}
		for (int i = 0; i < ints.length; i++) {
			assert count(vec, ints[i]) == count(ints, ints[i])
					: "sort(false) must keep every element as often as it occurs in the input.";
		}
		for (int i = 0; i < vec.size(); i++) {
			assert vec.elementAt(i) instanceof IntValue
					&& count(ints, ((IntValue) vec.elementAt(i)).val) > 0 : "sort(false) must not add elements.";
		}
	}

	// JBMC/CBMC treats all parameters as unconstrained nondeterministic inputs.
	// search returns x \in {ints[i] : i \in DOMAIN ints}, unsorted on ints and
	// sorted on sort(true).
	public static void verifySearch(final int[] ints, final int x) {
		if (ints == null) {
			// SKIP: A null array cannot supply the vector's elements.
			return;
		}
		final boolean member = count(ints, x) > 0;
		final IntValue elem = IntValue.gen(x);
		assert vec(ints).search(elem, false) == member
				: "An unsorted search must find exactly the vector's elements.";
		assert vec(ints).sort(true).search(elem, true) == member
				: "A sorted search must find exactly the vector's elements.";
	}

	// Must be at least --max-nondet-array-length. Do not wrap an array of the
	// input's length (new ValueVec(Value[])): when elementData has a symbolic
	// length, sort's writes into it inflate the SAT formula a hundredfold. With
	// three elements, JBMC then takes nine minutes per sort harness, and search
	// does not finish within 15 minutes; with a constant capacity, each harness
	// takes a few seconds.
	private static final int CAPACITY = 3;

	private static ValueVec vec(final int[] ints) {
		final ValueVec vec = new ValueVec(CAPACITY);
		for (int i = 0; i < ints.length; i++) {
			vec.addElement(IntValue.gen(ints[i]));
		}
		return vec;
	}

	private static int count(final int[] ints, final int x) {
		int n = 0;
		for (int i = 0; i < ints.length; i++) {
			if (ints[i] == x) {
				n++;
			}
		}
		return n;
	}

	private static int count(final ValueVec vec, final int x) {
		int n = 0;
		for (int i = 0; i < vec.size(); i++) {
			if (ValueHarness.isInt(vec.elementAt(i), x)) {
				n++;
			}
		}
		return n;
	}
}
