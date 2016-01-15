/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
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

package tlc2.module;

import org.junit.Assert;
import org.junit.Test;

import tlc2.value.FcnRcdValue;
import tlc2.value.IntValue;
import tlc2.value.TupleValue;
import tlc2.value.Value;

public class TLCTest {

	/**
	 * func2 == <<1,2,3>>
	 * ASSUME (3 :> 11 @@ func2) = <<1,2,11>>
	 */
	@Test
	public void testA() {
		final Value f = new FcnRcdValue(new Value[] { IntValue.gen(3) }, new Value[] { IntValue.gen(11) }, true);
		final Value g = new TupleValue(new Value[] { IntValue.gen(1), IntValue.gen(2), IntValue.gen(3) });

		final Value combined = TLC.CombineFcn(f, g);
		Assert.assertTrue(combined instanceof FcnRcdValue);
		final FcnRcdValue rcdVal = (FcnRcdValue) combined;
		// Have to normalize to bring values/domain into natural order expected by assertions below
		rcdVal.normalize();

		// domain
		Assert.assertEquals(3, rcdVal.domain.length);
		Assert.assertArrayEquals(new Value[] { IntValue.gen(1), IntValue.gen(2), IntValue.gen(3) }, rcdVal.domain);

		// values
		Assert.assertEquals(3, rcdVal.values.length);
		Assert.assertArrayEquals(new Value[] { IntValue.gen(1), IntValue.gen(2), IntValue.gen(11) }, rcdVal.values);
	}

	/**
	 * func2 == <<1,2,3>>
	 * ASSUME (4 :> 11 @@ func2) = <<1,2,3,11>>
	 */
	@Test
	public void testB() {
		final Value f = new FcnRcdValue(new Value[] { IntValue.gen(4) }, new Value[] { IntValue.gen(11) }, true);
		final Value g = new TupleValue(new Value[] { IntValue.gen(1), IntValue.gen(2), IntValue.gen(3), IntValue.gen(11) });

		final Value combined = TLC.CombineFcn(f, g);
		Assert.assertTrue(combined instanceof FcnRcdValue);
		final FcnRcdValue rcdVal = (FcnRcdValue) combined;
		// Have to normalize to bring values/domain into natural order expected by assertions below
		rcdVal.normalize();
		
		// domain
		Assert.assertEquals(4, rcdVal.domain.length);
		Assert.assertArrayEquals(new Value[] { IntValue.gen(1), IntValue.gen(2), IntValue.gen(3), IntValue.gen(4) },
				rcdVal.domain);

		// values
		Assert.assertEquals(4, rcdVal.values.length);
		Assert.assertArrayEquals(new Value[] { IntValue.gen(1), IntValue.gen(2), IntValue.gen(3), IntValue.gen(11) },
				rcdVal.values);
	}
}
