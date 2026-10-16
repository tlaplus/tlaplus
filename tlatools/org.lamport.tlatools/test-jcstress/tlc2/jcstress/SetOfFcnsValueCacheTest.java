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
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.SetOfFcnsValue;
import tlc2.value.impl.Value;

/**
 * The set [{2, 1} -> {4, 3}], which TLC has deep-normalized as it does before
 * it shares a value. One worker fills the cache fcnSet while another reads it.
 * See SetCupValueCacheTest and LazySets.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/439
 */
@JCStressTest
@Outcome(id = "1, 4", expect = Expect.ACCEPTABLE, desc = "The reader sees four elements.")
@Outcome(expect = Expect.FORBIDDEN, desc = "A worker saw the cache without its elements " + Codes.LEGEND + ".")
@State
public class SetOfFcnsValueCacheTest {

	private final SetOfFcnsValue set;

	public SetOfFcnsValueCacheTest() {
		set = new SetOfFcnsValue(new SetEnumValue(new Value[] { IntValue.gen(2), IntValue.gen(1) }, false),
				new SetEnumValue(new Value[] { IntValue.gen(4), IntValue.gen(3) }, false));
		set.deepNormalize();
	}

	@Actor
	public void publisher(final II_Result r) {
		r.r1 = LazySets.publish(set);
	}

	@Actor
	public void reader(final II_Result r) {
		r.r2 = LazySets.read(set);
	}
}
