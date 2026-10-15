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

import org.jetbrains.lincheck.datastructures.Operation;
import org.junit.Test;

import tlc2.value.RandomEnumerableValues;

/**
 * The set N == 0..29999 and the set S == {3, 1, 2}, whose elements are not
 * normalized. N \X N \X N \X S has more than 2^31 elements, which makes
 * RandomSubset(2, N \X N \X N \X S) enumerate it with BigInteger indices. A
 * worker that evaluates it while another worker fingerprints S must get the 2
 * tuples that it gets before or after the fingerprint, which differ in their
 * last components. Whether the indices need BigInteger is known once the
 * product of the sizes of the first three sets overflows, so TLC never asks S
 * for its size, which would have sorted S. The subset enumerator decodes each
 * index with the elements of S that it reads anew for each tuple.
 * Fingerprinting replaces those elements with sorted ones, so the enumerator
 * may decode the first index with the unsorted elements and the second with
 * the sorted ones.
 * 
 * @see SetOfTuplesFcnsRcdsValueRandomSubsetTest
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class SetOfTuplesValueBigRandomSubsetTest extends ValueLincheckTestCase {

	private static final SetEnumValue N = (SetEnumValue) new IntervalValue(0, 29_999).toSetEnum();

	private final SetEnumValue set = unsortedSet();

	@Override
	protected Value value() {
		return set;
	}

	@Operation
	public String randomSubset() {
		RandomEnumerableValues.reset();
		return new SetOfTuplesValue(new Value[] { N, N, N, set }).getRandomSubset(2).normalize().toString();
	}

	@Test
	public void fingerPrintAndRandomSubset() {
		modelCheckingParallel("fingerPrint", "randomSubset");
	}
}
