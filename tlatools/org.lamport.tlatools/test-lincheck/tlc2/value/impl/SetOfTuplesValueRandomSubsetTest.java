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
 * The set S == {3, 1, 2}, whose elements are not normalized. A worker that
 * evaluates RandomSubset(3, S \X {0}) while another worker fingerprints S
 * must still get all 3 tuples of S \X {0}. The subset enumerator decodes each
 * index with the elements of S that it reads anew for each tuple. If
 * fingerprinting replaced those elements with sorted ones in between, the same
 * index could decode to another tuple, and the enumerator would return a tuple
 * twice and omit another. Yet TLC asks S for its size before it creates the
 * enumerator, to tell whether the indices need BigInteger, and that sorts S.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class SetOfTuplesValueRandomSubsetTest extends ValueLincheckTestCase {

	static {
		// The enumerator computes, and caches, its parameters for a set of 3
		// elements in many more steps than Lincheck allows a worker to take.
		new SetOfTuplesValue(unsortedSet(), zero()).getRandomSubset(3);
	}

	private static SetEnumValue zero() {
		return new SetEnumValue(new Value[] { IntValue.gen(0) }, true);
	}

	private final SetEnumValue set;

	public SetOfTuplesValueRandomSubsetTest() {
		this(unsortedSet());
	}

	private SetOfTuplesValueRandomSubsetTest(final SetEnumValue set) {
		super(set);
		this.set = set;
	}

	@Operation
	public int randomSubset() {
		RandomEnumerableValues.reset();
		return ((SetEnumValue) new SetOfTuplesValue(set, zero()).getRandomSubset(3).normalize()).size();
	}

	@Test
	public void fingerPrintAndRandomSubset() {
		modelCheckingParallel("fingerPrint", "randomSubset");
	}
}
