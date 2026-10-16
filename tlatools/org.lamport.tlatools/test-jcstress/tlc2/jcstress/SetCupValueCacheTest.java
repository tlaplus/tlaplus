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

import tlc2.value.impl.IntValue;
import tlc2.value.impl.SetCupValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.Value;

/**
 * The set {3, 1, 2} \cup {5, 4}, which TLC has deep-normalized as it does
 * before it shares a value, so that its cache cupSet is SetEnumValue.DummyEnum.
 * One worker fills the cache, by computing the size of the set, while another
 * reads it. If SetCupValue#convertAndCache builds the cache in one synchronized
 * block and publishes it in another, and SetCupValue#toSetEnum reads it without
 * a lock, the reader may see the cache but elems as null (-1) or as an empty or
 * stale ValueVec. TLC as of 425dc60aa did so.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/439
 */
@JCStressTest
@Outcome(id = "5, 5", expect = Expect.ACCEPTABLE, desc = "Both workers see five elements.")
@Outcome(expect = Expect.FORBIDDEN, desc = "A worker saw the cache without its elements " + Codes.LEGEND + ".")
@State
public class SetCupValueCacheTest {

	private final SetCupValue set;

	public SetCupValueCacheTest() {
		set = new SetCupValue(
				new SetEnumValue(new Value[] { IntValue.gen(3), IntValue.gen(1), IntValue.gen(2) }, false),
				new SetEnumValue(new Value[] { IntValue.gen(5), IntValue.gen(4) }, false));
		set.deepNormalize();
	}

	@Actor
	public void publisher(final II_Result r) {
		try {
			r.r1 = set.size();
		} catch (Throwable e) {
			r.r1 = Codes.of(e);
		}
	}

	@Actor
	public void reader(final II_Result r) {
		try {
			r.r2 = ((SetEnumValue) set.toSetEnum()).elems.size();
		} catch (Throwable e) {
			r.r2 = Codes.of(e);
		}
	}
}
