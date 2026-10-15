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

import tlc2.module.Bags;
import tlc2.util.FP64;

/**
 * The set S == {3, 1, 2}, whose elements are not normalized. A worker that
 * evaluates SetToBag(S) while another worker sorts S must still get
 * (1 :> 1 @@ 2 :> 1 @@ 3 :> 1). If Bags#SetToBag reads the elements of S and
 * whether S is normalized one after the other, without a lock, it may copy
 * elements that the sort has only partly rearranged, and mark the copy as
 * normalized.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class BagsSetToBagTest extends ValueLincheckTestCase {

	private final SetEnumValue set = unsortedSet();

	@Override
	protected Value value() {
		return set;
	}

	@Operation
	public long setToBag() {
		return Bags.SetToBag(set).fingerPrint(FP64.New());
	}

	@Test
	public void fingerPrintAndSetToBag() {
		modelCheckingParallel("fingerPrint", "setToBag");
	}
}
