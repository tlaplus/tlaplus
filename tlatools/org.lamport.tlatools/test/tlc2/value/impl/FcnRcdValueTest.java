/*******************************************************************************
 * Copyright (c) 2021 Microsoft Research. All rights reserved.
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
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.fail;

import java.util.ArrayList;
import java.util.List;

import org.junit.BeforeClass;
import org.junit.Test;

import tlc2.module.TLCExt;
import tlc2.util.FP64;
import tlc2.value.RandomEnumerableValues;
import util.Assert.TLCRuntimeException;

public class FcnRcdValueTest {

	private static final Value[] getInts(final int from, final int to, final int offset) {
		final List<IntValue> l = new ArrayList<>();
		for (int i = from; i < to; i++) {
			l.add(IntValue.gen(offset + i));
		}
		return l.toArray(IntValue[]::new);
	}

	@BeforeClass
	public static void setup() {
		// Make test repeatable by setting random seed always to same value.
		RandomEnumerableValues.setSeed(15041980L);
		// Needed to insert elements into java.util.Set (because of hashcode) later to
		// detect duplicates.
		FP64.Init();
	}

	@Test
	public void testSelecEmpty() {
		FcnRcdValue rcdValue = new FcnRcdValue(new IntValue[0], new IntValue[0], false);
		rcdValue.select(IntValue.ValNegOne);
	}

	@Test
	public void testSelecNormalizedEmpty() {
		FcnRcdValue rcdValue = (FcnRcdValue) new FcnRcdValue(new IntValue[0], new IntValue[0], false).normalize();
		rcdValue.select(IntValue.ValNegOne);
	}

	@Test
	public void testSelect() {
		testSelect(false);
	}

	@Test
	public void testSelectNormalized() {
		testSelect(true);
	}

	private static void testSelect(final boolean normalize) {
		for (int upper = -64; upper < 64; upper++) {
			for (int lower = -64; lower < upper; lower++) {
				Value[] dom = getInts(lower, upper, 0);
				Value[] rng = getInts(lower, upper, 1024);

				FcnRcdValue rcdValue = new FcnRcdValue(dom, rng, false);
				if (normalize) {
					rcdValue.normalize();
				}

				for (int j = -128; j < 128; j++) {
					if (j < ((IntValue) dom[0]).val || j > ((IntValue) dom[dom.length - 1]).val) {
						// \A i \notin ...
						assertNull(rcdValue.select(IntValue.gen(j)));
					} else {
						// \A i \in ...
						IntValue val = (IntValue) rcdValue.select(IntValue.gen(j));
						assertNotNull(val);
						assertEquals(IntValue.gen(j + 1024), val);
					}
				}
			}
		}
	}
	
	/*
	 * #### Typed Model Values
	 * 
	 * One way that TLC finds bugs is by reporting an error if it tries to compare
	 * two incomparable values&mdash;for example, a string and a set. The use of
	 * model values can cause TLC to miss bugs because it will compare a model value
	 * to any value without complaining (finding it unequal to anything but itself).
	 * Typed model values have been introduced to solve this problem.
	 * 
	 * For any character &tau;, a model value whose name begins with the
	 * two-character string "&tau;\_" is defined to have type &tau;. For example,
	 * the model value _x\_1_ has type _x_. Any other model value is untyped. TLC
	 * treats untyped model values as before, being willing to compare them to
	 * anything. However it reports an error if it tries to compare a typed model
	 * value to anything other than a model value of the same type or an untyped
	 * model value. Thus, TLC will find the model value _x_1_ unequal to the model
	 * values _x_ab2_ and _none_, but will report an error if it tries to compare
	 * _x\_1_ to _a\_1_.
	 */
	
	@Test
	public void testSelectLinearSearchTypedMV() {
		final String str = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
		final List<ModelValue> l = new ArrayList<>();
		for (int i = 0; i < str.length(); i++) {
			l.add((ModelValue) TLCExt.tlcModelValue(new StringValue("A_" + str.charAt(i))));
		}
		
		final Value[] dom = l.toArray(ModelValue[]::new);
		final Value[] rng = getInts(0, dom.length, 0);
		final FcnRcdValue rcdValue = (FcnRcdValue) new FcnRcdValue(dom, rng, false).normalize();

		try {
			rcdValue.select(ModelValue.make("B_c"));
			fail("Comparison to typed model value should fail");
		} catch (TLCRuntimeException e) {
			assertEquals("Attempted to check equality of the differently-typed model values A_A and B_c", e.getMessage());
		}
		try {
			rcdValue.select(IntValue.ValNegOne);
			fail("Comparison to typed model value should fail");
		} catch (TLCRuntimeException e) {
			assertEquals("Attempted to check equality of typed model value A_A and non-model value\n"
					+ "-1", e.getMessage());
		}
		
		for (int i = 0; i < dom.length; i++) {
			IntValue val = (IntValue) rcdValue.select(dom[i]);
			assertNotNull(val);
			assertEquals(IntValue.gen(i), val);
		}
	}
	
	@Test
	public void testSelectBinarySearchTypedMV() {
		final String str = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
		final List<ModelValue> l = new ArrayList<>();
		for (int i = 0; i < str.length(); i++) {
			l.add((ModelValue) TLCExt.tlcModelValue(new StringValue("A_" + str.charAt(i))));
		}
		
		final Value[] dom = l.toArray(ModelValue[]::new);
		final Value[] rng = getInts(0, dom.length, 0);
		final FcnRcdValue rcdValue = (FcnRcdValue) new FcnRcdValue(dom, rng, false).normalize();

		try {
			rcdValue.select(ModelValue.make("B_c"));
			fail("Comparison to typed model value should fail");
		} catch (TLCRuntimeException e) {
			assertEquals("Attempted to compare the differently-typed model values A_Z and B_c", e.getMessage());
		}
		try {
			rcdValue.select(IntValue.ValNegOne);
			fail("Comparison to typed model value should fail");
		} catch (TLCRuntimeException e) {
			assertEquals("Attempted to compare the typed model value A_Z and non-model value\n"
					+ "-1", e.getMessage());
		}
		
		for (int i = 0; i < dom.length; i++) {
			IntValue val = (IntValue) rcdValue.select(dom[i]);
			assertNotNull(val);
			assertEquals(IntValue.gen(i), val);
		}
	}
}
