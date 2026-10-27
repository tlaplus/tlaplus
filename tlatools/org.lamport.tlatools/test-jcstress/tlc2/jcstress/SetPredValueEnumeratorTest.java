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
import static tlc2.value.impl.ValueFixtures.sum;

import org.openjdk.jcstress.annotations.Actor;
import org.openjdk.jcstress.annotations.Expect;
import org.openjdk.jcstress.annotations.JCStressTest;
import org.openjdk.jcstress.annotations.Outcome;
import org.openjdk.jcstress.annotations.State;
import org.openjdk.jcstress.infra.results.II_Result;

import tlc2.value.impl.IntervalValue;
import tlc2.value.impl.SetPredValue;

/**
 * The set S == {x \in 1..4 : x % 2 = 0}. A worker that enumerates S while
 * another worker computes the size of S must see exactly 2 and 4.
 * <p>
 * SetPredValue#size replaces the plain field inVal with the filtered set and
 * then sets the volatile converted. SetPredValue#elements reads converted and,
 * if false, the Enumerator reads inVal without a happens-before edge to the
 * write of inVal. If the reader sees the filtered set, which it then filters
 * again, its contents must have been published, or the reader fails (-1) or
 * misses elements. The x86 memory model hides this; run on AArch64.
 * 
 * @see SetPredValueConvertedTest
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
@JCStressTest
@Outcome(id = "2, 6", expect = Expect.ACCEPTABLE, desc = "The reader enumerated 2 and 4.")
@Outcome(expect = Expect.FORBIDDEN, desc = "The reader enumerated the wrong elements " + Codes.LEGEND + ".")
@State
public class SetPredValueEnumeratorTest {

	private final SetPredValue set = setPred(new IntervalValue(1, 4), X_IS_EVEN);

	@Actor
	public void publisher(final II_Result r) {
		r.r1 = Codes.catching(() -> set.size());
	}

	/** Returns the sum of the elements, which is 2 + 4 = 6. */
	@Actor
	public void reader(final II_Result r) {
		r.r2 = Codes.catching(() -> sum(set.elements()));
	}
}
