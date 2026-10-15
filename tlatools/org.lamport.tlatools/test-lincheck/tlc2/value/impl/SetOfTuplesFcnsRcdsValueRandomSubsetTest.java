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

import static tlc2.value.impl.ValueFixtures.sortedSet;

import org.jetbrains.lincheck.datastructures.Operation;
import org.junit.Test;

import tlc2.value.RandomEnumerableValues;
import util.UniqueString;

/**
 * The set S == {3, 1, 2}, whose elements are not normalized. A worker that
 * evaluates RandomSubset(3, S \X {0}), RandomSubset(3, [a : S]), or
 * RandomSubset(3, [{1} -> S]) while another worker fingerprints S must still
 * get all 3 tuples, records, or functions. The subset enumerator decodes each
 * index with the elements of S that it reads anew for each tuple, record, or
 * function. If fingerprinting replaced those elements with sorted ones in
 * between, the same index could decode to another one, and the enumerator
 * would return one twice and omit another. Yet TLC asks S for its size before
 * it creates the enumerator, to tell whether the indices need BigInteger, and
 * that sorts S.
 * 
 * @see SetOfTuplesValueBigRandomSubsetTest
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class SetOfTuplesFcnsRcdsValueRandomSubsetTest extends ValueLincheckTestCase {

	private static final UniqueString A = UniqueString.of("a");

	static {
		// The enumerators compute, and cache, their parameters for a set of 3
		// elements in many more steps than Lincheck allows a worker to take.
		tuples(unsortedSet()).getRandomSubset(3);
		rcds(unsortedSet()).getRandomSubset(3);
		fcns(unsortedSet()).getRandomSubset(3);
	}

	private static SetOfTuplesValue tuples(final SetEnumValue s) {
		return new SetOfTuplesValue(s, sortedSet(0));
	}

	private static SetOfRcdsValue rcds(final SetEnumValue s) {
		return new SetOfRcdsValue(new UniqueString[] { A }, new Value[] { s }, true);
	}

	private static SetOfFcnsValue fcns(final SetEnumValue s) {
		return new SetOfFcnsValue(sortedSet(1), s);
	}

	private final SetEnumValue set = unsortedSet();

	@Override
	protected Value value() {
		return set;
	}

	@Operation
	public int randomTuples() {
		RandomEnumerableValues.reset();
		return ((SetEnumValue) tuples(set).getRandomSubset(3).normalize()).size();
	}

	@Operation
	public int randomRcds() {
		RandomEnumerableValues.reset();
		return ((SetEnumValue) rcds(set).getRandomSubset(3).normalize()).size();
	}

	@Operation
	public int randomFcns() {
		RandomEnumerableValues.reset();
		return ((SetEnumValue) fcns(set).getRandomSubset(3).normalize()).size();
	}

	@Test
	public void fingerPrintAndRandomTuples() {
		modelCheckingParallel("fingerPrint", "randomTuples");
	}

	@Test
	public void fingerPrintAndRandomRcds() {
		modelCheckingParallel("fingerPrint", "randomRcds");
	}

	@Test
	public void fingerPrintAndRandomFcns() {
		modelCheckingParallel("fingerPrint", "randomFcns");
	}
}
