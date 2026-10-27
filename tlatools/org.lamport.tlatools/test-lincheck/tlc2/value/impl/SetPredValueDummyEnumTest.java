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

import static tlc2.value.impl.ValueFixtures.evaluatingTo;
import static tlc2.value.impl.ValueFixtures.ints;
import static tlc2.value.impl.ValueFixtures.setPred;

/**
 * The set {x \in {2, 1} : FALSE}, which is empty. deepNormalize sorts the set
 * {2, 1} that SetPredValue holds until fingerprinting replaces it with the
 * enumeration. A worker that enumerates the set must get no element whether it
 * reads {2, 1}, sorted or not, or the enumeration.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class SetPredValueDummyEnumTest extends LazySetDummyEnumTestCase {

	@Override
	protected EnumerableValue set() {
		return setPred(new SetEnumValue(ints(2, 1), false), evaluatingTo(BoolValue.ValFalse));
	}
}
