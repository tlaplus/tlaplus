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

import org.openjdk.jcstress.annotations.Actor;
import org.openjdk.jcstress.annotations.Expect;
import org.openjdk.jcstress.annotations.JCStressTest;
import org.openjdk.jcstress.annotations.Outcome;
import org.openjdk.jcstress.annotations.State;
import org.openjdk.jcstress.infra.results.II_Result;

import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.Value;

/**
 * The function [i \in 0..15 |-> 100 + i], whose domain is normalized, and which
 * two workers apply to 0. If FcnRcdValue#select builds an index of the domain
 * in one synchronized block and publishes it in another, and reads it without
 * a lock, a worker may see the index but not its entries, read -1, and fail
 * with "not in the domain of the function" (-2). TLC as of 425dc60aa did so for
 * functions with more than ten domain elements.
 * <p>
 * The argument is the first element of the domain, so that a worker that sees
 * an entry as 0, not yet initialized at all, still finds it, and lookupIndex
 * cannot loop forever.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/439
 */
@JCStressTest
@Outcome(id = "100, 100", expect = Expect.ACCEPTABLE, desc = "Both workers see f[0] = 100.")
@Outcome(expect = Expect.FORBIDDEN, desc = "A worker saw indexTbl without its entries " + Codes.LEGEND + ".")
@State
public class FcnRcdValueIndexTest {

	private static final int SIZE = 16;

	private final FcnRcdValue fcn;

	private final Value arg;

	public FcnRcdValueIndexTest() {
		final Value[] domain = new Value[SIZE];
		final Value[] values = new Value[SIZE];
		for (int i = 0; i < SIZE; i++) {
			domain[i] = IntValue.gen(i);
			values[i] = IntValue.gen(100 + i);
		}
		fcn = new FcnRcdValue(domain, values, true);
		arg = domain[0];
	}

	@Actor
	public void worker1(final II_Result r) {
		r.r1 = Codes.catching(() -> ((IntValue) fcn.select(arg)).val);
	}

	@Actor
	public void worker2(final II_Result r) {
		r.r2 = Codes.catching(() -> ((IntValue) fcn.select(arg)).val);
	}
}
