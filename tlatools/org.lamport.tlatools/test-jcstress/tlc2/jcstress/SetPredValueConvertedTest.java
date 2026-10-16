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

import static tlc2.value.impl.ValueFixtures.X_IS_EVEN;
import static tlc2.value.impl.ValueFixtures.setPred;

import org.openjdk.jcstress.annotations.Actor;
import org.openjdk.jcstress.annotations.Expect;
import org.openjdk.jcstress.annotations.JCStressTest;
import org.openjdk.jcstress.annotations.Outcome;
import org.openjdk.jcstress.annotations.State;
import org.openjdk.jcstress.infra.results.II_Result;

import tlc2.value.impl.IntValue;
import tlc2.value.impl.IntervalValue;
import tlc2.value.impl.SetPredValue;

/**
 * The set S == {x \in 1..4 : x % 2 = 0}. A worker that evaluates 1 \in S while
 * another worker computes the size of S must still get FALSE. If
 * SetPredValue#size stores the filtered set in inVal and then sets converted,
 * both without a lock or volatile, the reader may see converted but the old
 * inVal, check 1 against the unfiltered 1..4, and get TRUE (1), or see the new
 * inVal without its elements (-1).
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/439
 */
@JCStressTest
@Outcome(id = "2, 0", expect = Expect.ACCEPTABLE, desc = "The set has two elements, and 1 isn't one of them.")
@Outcome(id = "2, 1", expect = Expect.FORBIDDEN, desc = "The reader saw converted but the unfiltered inVal.")
@Outcome(expect = Expect.FORBIDDEN, desc = "A worker saw inVal without its elements " + Codes.LEGEND + ".")
@State
public class SetPredValueConvertedTest {

	private final SetPredValue set = setPred(new IntervalValue(1, 4), X_IS_EVEN);

	@Actor
	public void publisher(final II_Result r) {
		r.r1 = Codes.catching(() -> set.size());
	}

	@Actor
	public void reader(final II_Result r) {
		r.r2 = Codes.catching(() -> set.member(IntValue.gen(1)) ? 1 : 0);
	}
}
