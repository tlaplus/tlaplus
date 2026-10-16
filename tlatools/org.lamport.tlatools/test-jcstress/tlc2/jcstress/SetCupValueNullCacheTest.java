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
 * The set {1, 2, 3} \cup {4, 5}, whose cache cupSet is null. One worker fills
 * the cache, by computing the size of the set, while another reads it. If
 * SetCupValue#convertAndCache publishes a new SetEnumValue in cupSet without a
 * lock or volatile, the reader may see the cache but, because
 * SetEnumValue#elems isn't final, elems as null (-1) or as an empty ValueVec.
 * TLC as of 425dc60aa did so, although its lifecycle (#361) assumes that
 * workers never fill the cache of a shared value.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/439
 */
@JCStressTest
@Outcome(id = "5, 5", expect = Expect.ACCEPTABLE, desc = "Both workers see five elements.")
@Outcome(expect = Expect.FORBIDDEN, desc = "A worker saw the cache without its elements " + Codes.LEGEND + ".")
@State
public class SetCupValueNullCacheTest {

	// Sorted operands, so that enumerating them doesn't sort them in place,
	// which is the race of #1445, not of #439.
	private final SetCupValue set = new SetCupValue(
			new SetEnumValue(new Value[] { IntValue.gen(1), IntValue.gen(2), IntValue.gen(3) }, true),
			new SetEnumValue(new Value[] { IntValue.gen(4), IntValue.gen(5) }, true));

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
