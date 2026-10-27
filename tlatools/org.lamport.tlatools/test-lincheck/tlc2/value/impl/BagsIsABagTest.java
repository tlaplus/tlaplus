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

import static tlc2.value.impl.ValueFixtures.ints;

import org.jetbrains.lincheck.datastructures.Operation;
import org.junit.Test;

import tlc2.module.Bags;

/**
 * The function f == (3 :> 0 @@ 1 :> 10 @@ 2 :> 20), whose domain is not
 * normalized, and which is no bag because 3 has no copies in it. A worker that
 * evaluates IsABag(f) while another worker sorts f must still get FALSE.
 * FcnRcdValue#normalize first swaps 1 to the front, which briefly holds 10 at
 * both ends of the values of f. If Bags#IsABag reads the values of f then, it
 * misses 0 and gets TRUE.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class BagsIsABagTest extends ValueLincheckTestCase {

	private final FcnRcdValue bag = new FcnRcdValue(ints(3, 1, 2), ints(0, 10, 20), false);

	@Override
	protected Value value() {
		return bag;
	}

	@Operation
	public boolean isABag() {
		return Bags.IsABag(bag).getVal();
	}

	@Test
	public void fingerPrintAndIsABag() {
		modelCheckingParallel("fingerPrint", "isABag");
	}
}
