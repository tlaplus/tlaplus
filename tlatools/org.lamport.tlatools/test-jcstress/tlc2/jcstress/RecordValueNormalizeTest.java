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

import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import util.UniqueString;

/**
 * The record [c |-> 3, a |-> 1, b |-> 2], which isn't normalized, and which
 * three workers share. One normalizes it and selects a, the others select b and
 * c. All must see the values of the fields.
 * <p>
 * RecordValue#normalize sorts the final arrays names and values in place while
 * it holds the lock of the record, and then sets the volatile isNorm. Readers
 * that see isNorm search without the lock, the others hold it. A reader that
 * saw isNorm before the sorted arrays would pair a name with the value of
 * another field or not find the name (-2). The x86 memory model hides this;
 * run on AArch64.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
@JCStressTest
@Outcome(id = "1, 2, 3", expect = Expect.ACCEPTABLE, desc = "All workers saw the values of the fields.")
@Outcome(expect = Expect.FORBIDDEN, desc = "A worker saw a partially sorted record " + Codes.LEGEND + ".")
@State
public class RecordValueNormalizeTest {

	private static final StringValue A = new StringValue("a");

	private static final StringValue B = new StringValue("b");

	private static final StringValue C = new StringValue("c");

	private final RecordValue rcd = new RecordValue(
			new UniqueString[] { UniqueString.of("c"), UniqueString.of("a"), UniqueString.of("b") }, ints(3, 1, 2),
			false);

	@Actor
	public void normalizer(final III_Result r) {
		r.r1 = Codes.catching(() -> {
			rcd.normalize();
			return ((IntValue) rcd.select(A)).val;
		});
	}

	@Actor
	public void reader1(final III_Result r) {
		r.r2 = Codes.catching(() -> ((IntValue) rcd.select(B)).val);
	}

	@Actor
	public void reader2(final III_Result r) {
		r.r3 = Codes.catching(() -> ((IntValue) rcd.select(C)).val);
	}
}
