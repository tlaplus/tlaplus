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
package tlc2.jcstress;

import static tlc2.value.impl.ValueFixtures.ints;

import org.openjdk.jcstress.annotations.Actor;
import org.openjdk.jcstress.annotations.Expect;
import org.openjdk.jcstress.annotations.JCStressTest;
import org.openjdk.jcstress.annotations.Outcome;
import org.openjdk.jcstress.annotations.State;
import org.openjdk.jcstress.infra.results.III_Result;

import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;

/**
 * The function (3 :> 30 @@ 1 :> 10 @@ 2 :> 20), whose domain isn't normalized,
 * and which three workers share. One normalizes it and applies it to 1, the
 * others apply it to 2 and 3. All must see the values of the function.
 * <p>
 * FcnRcdValue#normalize sorts the final arrays domain and values in place
 * while it holds the lock of the function, and then sets the volatile isNorm.
 * FcnRcdValue#select binary-searches snapshot(), which is the function itself
 * if isNorm, and otherwise a copy taken under the lock. A reader that saw isNorm
 * before the sorted arrays would pair an argument with the value of another or
 * not find it (-2). The x86 memory model hides this; run on AArch64.
 * 
 * @see FcnRcdValueIndexTest
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
@JCStressTest
@Outcome(id = "10, 20, 30", expect = Expect.ACCEPTABLE, desc = "All workers saw the values of the function.")
@Outcome(expect = Expect.FORBIDDEN, desc = "A worker saw a partially sorted function " + Codes.LEGEND + ".")
@State
public class FcnRcdValueNormalizeTest {

	private final FcnRcdValue fcn = new FcnRcdValue(ints(3, 1, 2), ints(30, 10, 20), false);

	@Actor
	public void normalizer(final III_Result r) {
		r.r1 = Codes.catching(() -> {
			fcn.normalize();
			return ((IntValue) fcn.select(IntValue.gen(1))).val;
		});
	}

	@Actor
	public void reader1(final III_Result r) {
		r.r2 = Codes.catching(() -> ((IntValue) fcn.select(IntValue.gen(2))).val);
	}

	@Actor
	public void reader2(final III_Result r) {
		r.r3 = Codes.catching(() -> ((IntValue) fcn.select(IntValue.gen(3))).val);
	}
}
