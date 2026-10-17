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
package tlc2.tool;

import static org.junit.Assert.assertFalse;

import org.junit.Test;

import tlc2.output.EC;

/**
 * Regression test for https://github.com/tlaplus/tlaplus/issues/1445
 *
 * SpecProcessor#processConfigProps unrolls the \A of a property and binds a lazy
 * set or function (SetPredValue, FcnLambdaValue) over an infinite domain in the
 * context of an invariant that all workers share. Publishing the value cannot
 * normalize it. The value evaluates its body in the context of a LET, which
 * binds a LazyValue, and in the empty state, so the value of the LET that
 * LazyValue#getValue caches for the first worker applies to all workers.
 * LazyValue#getValue caches the value without normalizing it, and
 * workers race to normalize the cached value, which drops elements from it and
 * causes a bogus violation of the invariant. Break in LazyValue#getValue.
 */
public class Github1445fTest extends Github1445TestCase {

	public Github1445fTest() {
		super("Github1445f");
	}

	@Test
	public void testSpec() {
		assertFalse(recorder.recorded(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR));
		// 8 initial states and 8 * 2048 successor states. Each of the latter also
		// generates itself by stuttering.
		assertSuccess("32776", "16392", "0");
	}
}
