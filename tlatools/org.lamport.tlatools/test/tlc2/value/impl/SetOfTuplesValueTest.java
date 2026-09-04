/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
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
package tlc2.value.impl;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.HashSet;
import java.util.List;

import org.junit.BeforeClass;
import org.junit.Test;

import tlc2.TLCGlobals;
import tlc2.util.FP64;
import tlc2.value.RandomEnumerableValues;
import tlc2.value.impl.IntervalValue;
import tlc2.value.impl.SetOfTuplesValue;
import util.Assert;

public class SetOfTuplesValueTest {

	@BeforeClass
	public static void setup() {
		// Make test repeatable by setting random seed always to same value.
		RandomEnumerableValues.setSeed(15041980L);
		// Needed to insert elements into java.util.Set (because of hashcode) below to
		// detect duplicates.
		FP64.Init();
	}

	@Test
	public void testToStringLazy() {
		// Force toString representation to be lazy.
		TLCGlobals.enumBound = 1;
		
		final IntervalValue intVal = new IntervalValue(1, 2);
		final SetOfTuplesValue inner = new SetOfTuplesValue(intVal, intVal);
		final SetOfTuplesValue outter = new SetOfTuplesValue(inner, inner);
		assertTrue(outter.toString().contains("\\X"));
		assertEquals("((1..2 \\X 1..2) \\X (1..2 \\X 1..2))", outter.toString());
	}

	// 1..4000 \X 1..4000 \X 1..4000 \X {} = {}, which the cardinality of the other
	// components must not hide: 4000^3 exceeds Integer.MAX_VALUE, so stopping at the
	// first overflow reports an empty product as too large to count.
	@Test
	public void testEmptyComponentBehindOverflowingComponents() {
		final Value big = new IntervalValue(1, 4000);
		final SetOfTuplesValue product = new SetOfTuplesValue(
				new Value[] { big, big, big, new SetEnumValue() });

		assertEquals(0, product.size());
		assertEquals(0, product.elements(3).all().size());
		assertEquals(0, product.getRandomSubset(3).size());
	}

	// Randomization!RandomSubset(k, S_1 \X ... \X S_n) picks k elements of the product
	// without enumerating it, which is what SetOfTuplesValue inherits from
	// SetOfFcnsOrRcdsValue. Neither product below can be enumerated: the first one has
	// more elements than TLCGlobals.setBound, and the cardinality of the second one
	// exceeds Integer.MAX_VALUE, i.e. size() cannot even report it.

	@Test
	public void testRandomSubsetBeyondSetBound() {
		// Cardinality(1..200 \X 1..200 \X 1..200) = 8000000
		final IntervalValue iv = new IntervalValue(1, 200);
		final SetOfTuplesValue product = new SetOfTuplesValue(new Value[] { iv, iv, iv });

		assertFalse(product.needBigInteger());
		assertEquals(8000000, product.size());
		assertTrue(product.size() > TLCGlobals.setBound);

		assertTrue(product.elements(1000) instanceof SetOfFcnsOrRcdsValue.SubsetEnumerator);
		assertRandomSubset(product, 1000);
	}

	@Test
	public void testRandomSubsetBeyondIntMaxValue() {
		// Cardinality(1..4000 \X 1..4000 \X 1..4000) = 64000000000
		final IntervalValue iv = new IntervalValue(1, 4000);
		final SetOfTuplesValue product = new SetOfTuplesValue(new Value[] { iv, iv, iv });

		assertTrue(product.needBigInteger());
		try {
			product.size();
			fail("size() has to overflow for a product of more than Integer.MAX_VALUE elements.");
		} catch (Assert.TLCRuntimeException expected) {
			// Which is why the enumeration below indexes the product with BigInteger.
		}

		assertTrue(product.elements(1000) instanceof SetOfFcnsOrRcdsValue.BigIntegerSubsetEnumerator);
		assertRandomSubset(product, 1000);
	}

	private static void assertRandomSubset(final SetOfTuplesValue product, final int k) {
		final List<Value> values = product.elements(k).all();

		// k distinct elements...
		assertEquals(k, values.size());
		assertEquals(k, new HashSet<>(values).size());

		// ...each of which is a tuple of the product.
		for (Value v : values) {
			assertTrue(product.member(v));
		}

		assertEquals(k, product.getRandomSubset(k).size());
	}
}
