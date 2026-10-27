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
import static tlc2.value.impl.ValueFixtures.sum;

import org.openjdk.jcstress.annotations.Actor;
import org.openjdk.jcstress.annotations.Expect;
import org.openjdk.jcstress.annotations.JCStressTest;
import org.openjdk.jcstress.annotations.Outcome;
import org.openjdk.jcstress.annotations.State;
import org.openjdk.jcstress.infra.results.III_Result;

import tlc2.value.impl.IntValue;
import tlc2.value.impl.SetEnumValue;

/**
 * The set {3, 1, 2, 1}, which isn't normalized, and which three workers share.
 * One computes its size, which normalizes the set, another checks 2 \in S, and
 * the third enumerates S. All must see the three elements 1, 2, and 3.
 * <p>
 * SetEnumValue#normalize sorts a copy of elems and then publishes it through
 * the volatile elems and isNorm. Readers read isNorm before elems. If the
 * sorted copy were published before it is complete, a reader could see it
 * without its elements (-1), unsorted while isNorm is true (and miss 2 in the
 * binary search), or with the duplicate 1. The x86 memory model hides most
 * reorderings; run on AArch64.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
@JCStressTest
@Outcome(id = "3, 1, 6", expect = Expect.ACCEPTABLE, desc = "All workers saw {1, 2, 3}.")
@Outcome(expect = Expect.FORBIDDEN, desc = "A worker saw a partially normalized set " + Codes.LEGEND + ".")
@State
public class SetEnumValueNormalizeTest {

	private final SetEnumValue set = new SetEnumValue(ints(3, 1, 2, 1), false);

	@Actor
	public void size(final III_Result r) {
		r.r1 = Codes.catching(() -> set.size());
	}

	@Actor
	public void member(final III_Result r) {
		r.r2 = Codes.catching(() -> set.member(IntValue.gen(2)) ? 1 : 0);
	}

	/** Returns the sum of the elements, which is 1 + 2 + 3 = 6. */
	@Actor
	public void enumerate(final III_Result r) {
		r.r3 = Codes.catching(() -> sum(set.elements()));
	}
}
