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
 * The bag B == (3 :> 30 @@ 1 :> 10 @@ 2 :> 20), whose domain is not
 * normalized. A worker that evaluates BagToSet(B) while another worker sorts B
 * must still get {1, 2, 3}. If Bags#BagToSet wraps the domain of B, not a copy,
 * in a set while another worker still sorts the domain in place, the set may
 * contain 3 twice.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class BagsBagToSetTest extends ValueLincheckTestCase {

	private final FcnRcdValue bag;

	public BagsBagToSetTest() {
		this(unsortedFcn());
	}

	private BagsBagToSetTest(final FcnRcdValue bag) {
		super(bag);
		this.bag = bag;
	}

	@Operation
	public long bagToSet() {
		return Bags.BagToSet(bag).fingerPrint(FP64.New());
	}

	@Test
	public void fingerPrintAndBagToSet() {
		modelCheckingParallel("fingerPrint", "bagToSet");
	}
}
