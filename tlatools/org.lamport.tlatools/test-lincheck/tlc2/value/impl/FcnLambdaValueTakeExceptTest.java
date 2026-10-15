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
import static tlc2.value.impl.ValueFixtures.sevens;

import org.jetbrains.lincheck.datastructures.Operation;
import org.junit.Test;

/**
 * The function f == [x \in 1..3 |-> 7], which TLC has not yet converted to a
 * FcnRcdValue. A worker that evaluates [f EXCEPT ![2] = 99][2] while another
 * worker fingerprints f must still get 99. Fingerprinting converts f to a
 * FcnRcdValue and caches it in f. If FcnLambdaValue#takeExcept finds no cache,
 * but its copy of f then copies the cache that the other worker just
 * published, the copy evaluates to the cache and ignores the EXCEPT, so the
 * first worker gets 7.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class FcnLambdaValueTakeExceptTest extends ValueLincheckTestCase {

	private final FcnLambdaValue fcn = sevens();

	@Override
	protected Value value() {
		return fcn;
	}

	private static ValueExcept except() {
		return new ValueExcept(ints(2), IntValue.gen(99));
	}

	@Operation
	public int takeExcept() {
		return ((IntValue) ((FunctionValue) fcn.takeExcept(except())).select(IntValue.gen(2))).val;
	}

	@Operation
	public int takeExcepts() {
		return ((IntValue) ((FunctionValue) fcn.takeExcept(new ValueExcept[] { except() }))
				.select(IntValue.gen(2))).val;
	}

	@Test
	public void fingerPrintAndTakeExcept() {
		modelCheckingParallel("fingerPrint", "takeExcept");
	}

	@Test
	public void fingerPrintAndTakeExcepts() {
		modelCheckingParallel("fingerPrint", "takeExcepts");
	}
}
