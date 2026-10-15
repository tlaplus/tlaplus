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

import tlc2.util.FP64;

/**
 * The lazy set that the subclass creates. A worker that evaluates the set while
 * another worker deep-normalizes it must still get its elements, so
 * deepNormalize must not overwrite the cache that fingerprinting fills.
 * <p>
 * The subclasses enumerate their sets in order, so that sorting the cache cannot
 * change it, and only an overwrite can fail the test.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public abstract class LazySetDummyEnumTestCase extends ValueLincheckTestCase {

	private final EnumerableValue set = set();

	/**
	 * The lazy set, which this calls once for every interleaving.
	 */
	protected abstract EnumerableValue set();

	@Override
	protected final Value value() {
		return set;
	}

	@Operation
	public void deepNormalize() {
		set.deepNormalize();
	}

	/**
	 * Fills the cache for toSetEnum and elements, which only read it. Only their
	 * results show whether they read an overwritten cache, because fingerPrint,
	 * which this calls, may read it too.
	 */
	@Operation
	public void fillCache() {
		try {
			set.fingerPrint(FP64.New());
		} catch (NullPointerException e) {
		}
	}

	@Operation
	public int toSetEnum() {
		return ((SetEnumValue) set.toSetEnum()).elems.size();
	}

	@Operation
	public int elements() {
		final ValueEnumeration elements = set.elements();
		int n = 0;
		while (elements.nextElement() != null) {
			n++;
		}
		return n;
	}

	@Test
	public void deepNormalizeAndFingerPrint() {
		modelCheckingParallel("deepNormalize", "fingerPrint");
	}

	@Test
	public void deepNormalizeAndToSetEnum() {
		modelCheckingParallel(200_000, "deepNormalize", "fillCache", "toSetEnum");
	}

	@Test
	public void deepNormalizeAndElements() {
		modelCheckingParallel(200_000, "deepNormalize", "fillCache", "elements");
	}
}
