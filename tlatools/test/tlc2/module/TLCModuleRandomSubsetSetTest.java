/*******************************************************************************
 * Copyright (c) 20178 Microsoft Research. All rights reserved.
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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.BeforeClass;
import org.junit.Test;

import tlc2.tool.EvalException;
import tlc2.value.Enumerable;
import tlc2.value.EnumerableValue;
import tlc2.value.IntValue;
import tlc2.value.IntervalValue;
import tlc2.value.SetEnumValue;
import tlc2.value.StringValue;
import tlc2.value.Value;

public class TLCModuleRandomSubsetSetTest {
	
	@BeforeClass
	public static void setup() {
		// Make test repeatable by setting random seed always to same value. 
		EnumerableValue.enumFractionSeed = 15041980L;
		EnumerableValue.resetRandom();
	}

	@Test
	public void testV1Valid() {
		final Enumerable randomSubsetSet = (Enumerable) TLC.RandomSubsetSet(IntValue.gen(42), new StringValue("0.1"),
				new IntervalValue(1, 42));

		assertNotNull(randomSubsetSet);
		assertEquals(42, randomSubsetSet.size());
	}

	@Test
	public void testV1Negative() {
		final Value v1 = IntValue.gen(-42);
		try {
			TLC.RandomSubsetSet(v1, new StringValue("0.1"), new IntervalValue(1, 42));
		} catch (final EvalException ee) {
			assertTrue(ee.getMessage().contains("-42"));
			return;
		}
		fail();
	}

	@Test
	public void testV1Zero() {
		final Value v1 = IntValue.gen(0);
		final Enumerable randomSubsetSet = (Enumerable) TLC.RandomSubsetSet(v1, new StringValue("0.1"),
				new IntervalValue(1, 42));

		assertNotNull(randomSubsetSet);
		assertEquals(0, randomSubsetSet.size());
	}
	
	@Test
	public void testV1NoIntValue() {
		final Value v1 = new StringValue("52");
		try {
			TLC.RandomSubsetSet(v1, new StringValue("0.1"), new IntervalValue(1, 42));
		} catch (final EvalException ee) {
			assertTrue(ee.getMessage().contains("\"52\""));
			return;
		}
		fail();
	}

	@Test
	public void testV2Zero() {
		final Enumerable randomSubsetSet = (Enumerable) TLC.RandomSubsetSet(IntValue.gen(23), new StringValue("0"),
				new IntervalValue(1, 42));
		assertEquals(1, randomSubsetSet.size());
		// empty set is only member
		assertTrue(randomSubsetSet.member(new SetEnumValue()));
	}

	@Test
	public void testV2Negative() {
		try {
			TLC.RandomSubsetSet(IntValue.gen(23), new StringValue("-1"), new IntervalValue(1, 42));
		} catch (final EvalException ee) {
			assertTrue(ee.getMessage().contains("-1"));
			return;
		}
		fail();
	}

	@Test
	public void testV2Larger1() {
		try {
			TLC.RandomSubsetSet(IntValue.gen(23), new StringValue("1.1"), new IntervalValue(1, 42));
		} catch (final EvalException ee) {
			assertTrue(ee.getMessage().contains("1.1"));
			return;
		}
		fail();
	}
	
	@Test
	public void testV3Empty() {
		try {
			TLC.RandomSubsetSet(IntValue.gen(42), new StringValue("1E-1"), new SetEnumValue());
		} catch (final EvalException ee) {
			assertTrue(ee.getMessage().contains("2^0"));
			return;
		}
		fail();
	}
	
	@Test
	public void testV3AstronomicallyLarge() {
		final Enumerable randomSubsetSet = (Enumerable) TLC.RandomSubsetSet(IntValue.gen(42), new StringValue("1E-1"),
				new IntervalValue(1, 256));

		assertNotNull(randomSubsetSet);
		assertEquals(42, randomSubsetSet.size());
	}
	
	@Test
	public void testV3isInfinite() {
		try {
			TLC.RandomSubsetSet(IntValue.gen(42), new StringValue("1E-1"), Naturals.Nat());
		} catch (final EvalException ee) {
			assertTrue(ee.getMessage().contains(
					"The third argument of RandomSubsetSet should be a finite set, but instead it is:\nNat"));
			return;
		}
		fail();
	}
}
