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
 * normalized. A worker that evaluates B (+) (4 :> 40) while another worker
 * sorts B must still get (1 :> 10 @@ 2 :> 20 @@ 3 :> 30 @@ 4 :> 40). If
 * Bags#BagCup reads the domain and the values of B one after the other, without
 * a lock, it may pair a sorted domain with unsorted values, or copy 3 twice.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class BagsBagCupTest extends ValueLincheckTestCase {

	private final FcnRcdValue bag;

	private final FcnRcdValue other = new FcnRcdValue(new Value[] { IntValue.gen(4) },
			new Value[] { IntValue.gen(40) }, true);

	public BagsBagCupTest() {
		this(unsortedFcn());
	}

	private BagsBagCupTest(final FcnRcdValue bag) {
		super(bag);
		this.bag = bag;
	}

	@Operation
	public long bagCup() {
		return Bags.BagCup(bag, other).fingerPrint(FP64.New());
	}

	@Test
	public void fingerPrintAndBagCup() {
		modelCheckingParallel("fingerPrint", "bagCup");
	}
}
