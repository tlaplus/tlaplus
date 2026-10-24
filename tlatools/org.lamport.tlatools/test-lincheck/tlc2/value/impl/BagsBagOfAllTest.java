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
import tlc2.util.Vect;

/**
 * The bag B == (3 :> 30 @@ 1 :> 10 @@ 2 :> 20), whose domain is not
 * normalized, and the operator F with F(1) = F(2) = 0 and F(3) = 1. A worker
 * that evaluates BagOfAll(F, B) while another worker sorts B must still get
 * (0 :> 30 @@ 1 :> 30). If Bags#BagOfAll reads the domain and the counts of B
 * while FcnRcdValue#normalize sorts them in place, it may pair an element with
 * the count of another.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class BagsBagOfAllTest extends ValueLincheckTestCase {

	private static final OpRcdValue F;

	static {
		final Vect<Value[]> domain = new Vect<>();
		final Vect<Value> values = new Vect<>();
		for (int i = 1; i <= 3; i++) {
			domain.addElement(new Value[] { IntValue.gen(i) });
			values.addElement(IntValue.gen(i == 3 ? 1 : 0));
		}
		F = new OpRcdValue(domain, values);
	}

	private final FcnRcdValue bag;

	public BagsBagOfAllTest() {
		this(unsortedFcn());
	}

	private BagsBagOfAllTest(final FcnRcdValue bag) {
		super(bag);
		this.bag = bag;
	}

	@Operation
	public long bagOfAll() {
		return Bags.BagOfAll(F, bag).fingerPrint(FP64.New());
	}

	@Test
	public void fingerPrintAndBagOfAll() {
		modelCheckingParallel("fingerPrint", "bagOfAll");
	}
}
