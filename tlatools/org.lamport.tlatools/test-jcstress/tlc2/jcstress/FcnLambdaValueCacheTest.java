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

import static tlc2.value.impl.ValueFixtures.sevensExcept2;

import org.openjdk.jcstress.annotations.Actor;
import org.openjdk.jcstress.annotations.Expect;
import org.openjdk.jcstress.annotations.JCStressTest;
import org.openjdk.jcstress.annotations.Outcome;
import org.openjdk.jcstress.annotations.State;
import org.openjdk.jcstress.infra.results.II_Result;

import tlc2.value.impl.FcnLambdaValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;

/**
 * The function f == [[x \in 1..3 |-> 7] EXCEPT ![2] = 99]. A worker that
 * evaluates f[2] while another worker converts f to a FcnRcdValue must still
 * get 99. If FcnLambdaValue#toFcnRcd publishes the FcnRcdValue in fcnRcd before
 * it applies the EXCEPT, the reader may get 7, and if it publishes fcnRcd
 * without a lock or volatile, the reader may see fcnRcd without its values
 * (-1).
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/439
 */
@JCStressTest
@Outcome(id = "99, 99", expect = Expect.ACCEPTABLE, desc = "Both workers see f[2] = 99.")
@Outcome(id = "99, 7", expect = Expect.FORBIDDEN, desc = "The reader saw fcnRcd before the EXCEPT.")
@Outcome(expect = Expect.FORBIDDEN, desc = "A worker saw fcnRcd without its values " + Codes.LEGEND + ".")
@State
public class FcnLambdaValueCacheTest {

	private final FcnLambdaValue fcn = sevensExcept2();

	@Actor
	public void publisher(final II_Result r) {
		r.r1 = Codes.catching(() -> ((IntValue) ((FcnRcdValue) fcn.toFcnRcd()).select(IntValue.gen(2))).val);
	}

	@Actor
	public void reader(final II_Result r) {
		r.r2 = Codes.catching(() -> ((IntValue) fcn.select(IntValue.gen(2))).val);
	}
}
