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

import static tlc2.value.impl.ValueFixtures.X_IS_EVEN;
import static tlc2.value.impl.ValueFixtures.ints;
import static tlc2.value.impl.ValueFixtures.setPred;

import org.jetbrains.lincheck.datastructures.Operation;
import org.junit.Test;

/**
 * The set S == {x \in {4, 1, 2, 3} : x % 2 = 0}, which TLC has not yet
 * enumerated. A worker that enumerates S while another worker fingerprints S
 * must still get 4 and 2, in either order, and in the order 2, 4 if it
 * normalizes S first. Fingerprinting replaces the set {4, 1, 2, 3} in S with
 * the enumeration of S. SetPredValue#elements and SetPredValue#normalize read
 * the set that S holds without converting S, so they may read either set.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class SetPredValueElementsTest extends ValueLincheckTestCase {

	private final SetPredValue set = setPred(new SetEnumValue(ints(4, 1, 2, 3), false), X_IS_EVEN);

	@Override
	protected Value value() {
		return set;
	}

	@Operation
	public String elements() {
		return enumerate(set.elements());
	}

	@Operation
	public String normalizeAndElements() {
		set.normalize();
		return elements();
	}

	@Test
	public void fingerPrintAndElements() {
		modelCheckingParallel("fingerPrint", "elements");
	}

	@Test
	public void fingerPrintAndNormalizeAndElements() {
		modelCheckingParallel("fingerPrint", "normalizeAndElements");
	}
}
