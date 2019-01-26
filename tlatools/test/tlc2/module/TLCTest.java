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

import java.util.HashSet;
import java.util.Set;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import tlc2.util.FP64;
import tlc2.value.impl.Enumerable;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.IntervalValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueEnumeration;

public class TLCTest {

	@BeforeClass
	public static void setup() {
		FP64.Init();
	}
	
	/**
	 * func2 == <<1,2,3>>
	 * ASSUME (3 :> 11 @@ func2) = <<1,2,11>>
	 */
	@Test
	public void testA() {
		final Value f = new FcnRcdValue(new Value [] { IntValue.gen(3) }, new Value [] { IntValue.gen(11) }, true);
		final Value g = new TupleValue(new Value [] { IntValue.gen(1), IntValue.gen(2), IntValue.gen(3) });

		final Value  combined = TLC.CombineFcn(f, g);
		Assert.assertTrue(combined instanceof FcnRcdValue);
		final FcnRcdValue rcdVal = (FcnRcdValue) combined;
		// Have to normalize to bring values/domain into natural order expected by assertions below
		rcdVal.normalize();

		// domain
		Assert.assertEquals(3, rcdVal.domain.length);
		Assert.assertArrayEquals(new Value [] { IntValue.gen(1), IntValue.gen(2), IntValue.gen(3) }, rcdVal.domain);

		// values
		Assert.assertEquals(3, rcdVal.values.length);
		Assert.assertArrayEquals(new Value [] { IntValue.gen(1), IntValue.gen(2), IntValue.gen(11) }, rcdVal.values);
	}

	/**
	 * func2 == <<1,2,3>>
	 * ASSUME (4 :> 11 @@ func2) = <<1,2,3,11>>
	 */
	@Test
	public void testB() {
		final Value f = new FcnRcdValue(new Value [] { IntValue.gen(4) }, new Value [] { IntValue.gen(11) }, true);
		final Value g = new TupleValue(new Value [] { IntValue.gen(1), IntValue.gen(2), IntValue.gen(3), IntValue.gen(11) });

		final Value  combined = TLC.CombineFcn(f, g);
		Assert.assertTrue(combined instanceof FcnRcdValue);
		final FcnRcdValue rcdVal = (FcnRcdValue) combined;
		// Have to normalize to bring values/domain into natural order expected by assertions below
		rcdVal.normalize();
		
		// domain
		Assert.assertEquals(4, rcdVal.domain.length);
		Assert.assertArrayEquals(new Value [] { IntValue.gen(1), IntValue.gen(2), IntValue.gen(3), IntValue.gen(4) },
				rcdVal.domain);

		// values
		Assert.assertEquals(4, rcdVal.values.length);
		Assert.assertArrayEquals(new Value [] { IntValue.gen(1), IntValue.gen(2), IntValue.gen(3), IntValue.gen(11) },
				rcdVal.values);
	}

	@Test
	public void testPermutations() {
		final SetEnumValue in = (SetEnumValue) new IntervalValue(1, 5).toSetEnum();
		Assert.assertEquals(5, in.size());
		
		final Value  permutations = TLC.Permutations(in);
		Assert.assertTrue(permutations instanceof Enumerable);
		Assert.assertEquals(120, permutations.size());

		final Set<Value > values = new HashSet<>(permutations.size());
		
		final ValueEnumeration elements = ((Enumerable) permutations).elements();
		Value  val = null;
		while ((val = elements.nextElement()) != null) {
			Assert.assertEquals(in.size(), val.size());
			values.add(val);
		}
		
		Assert.assertEquals(120, values.size());
	}
}
