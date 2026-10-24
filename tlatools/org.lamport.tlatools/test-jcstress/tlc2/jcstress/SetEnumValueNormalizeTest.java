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
import org.openjdk.jcstress.infra.results.III_Result;

import tlc2.value.impl.IntValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueEnumeration;

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

	private final SetEnumValue set = new SetEnumValue(
			new Value[] { IntValue.gen(3), IntValue.gen(1), IntValue.gen(2), IntValue.gen(1) }, false);

	@Actor
	public void size(final III_Result r) {
		try {
			r.r1 = set.size();
		} catch (Throwable e) {
			r.r1 = Codes.of(e);
		}
	}

	@Actor
	public void member(final III_Result r) {
		try {
			r.r2 = set.member(IntValue.gen(2)) ? 1 : 0;
		} catch (Throwable e) {
			r.r2 = Codes.of(e);
		}
	}

	/** Returns the sum of the elements, which is 1 + 2 + 3 = 6. */
	@Actor
	public void enumerate(final III_Result r) {
		try {
			final ValueEnumeration e = set.elements();
			int sum = 0;
			Value elem;
			while ((elem = e.nextElement()) != null) {
				sum += ((IntValue) elem).val;
			}
			r.r3 = sum;
		} catch (Throwable e) {
			r.r3 = Codes.of(e);
		}
	}
}
