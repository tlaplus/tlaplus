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

import tlc2.util.FP64;

/**
 * The function f == (3 :> 30 @@ 1 :> 10 @@ 2 :> 20), whose domain is not
 * normalized. A worker that evaluates [f EXCEPT ![1] = 11] while another worker
 * sorts f must still get (1 :> 11 @@ 2 :> 20 @@ 3 :> 30). If
 * FcnRcdValue#takeExcept reads the domain, the values, and whether f is
 * normalized one after the other, without a lock, it may copy a domain that the
 * sort has only partly rearranged, pair the domain with values in another
 * order, or mark an unsorted copy as normalized.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class FcnRcdValueExceptTest extends ValueLincheckTestCase {

	private final FcnRcdValue fcn = unsortedFcn();

	@Override
	protected Value value() {
		return fcn;
	}

	@Operation
	public long takeExcept() {
		return fcn.takeExcept(new ValueExcept(ints(1), IntValue.gen(11))).fingerPrint(FP64.New());
	}

	@Test
	public void fingerPrintAndTakeExcept() {
		modelCheckingParallel("fingerPrint", "takeExcept");
	}
}
