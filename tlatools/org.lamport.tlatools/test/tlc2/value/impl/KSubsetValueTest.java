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

import java.util.stream.IntStream;

import org.junit.Test;

import tlc2.util.Combinatorics;
import tlc2.util.FP64;

public class KSubsetValueTest {
	
	@Test
	public void testEnumerateN32() {
		final IntervalValue iv = new IntervalValue(1, 32);
		assertEquals(32, iv.size());

		final KSubsetValue kSubset = new KSubsetValue(2, iv);
		final SetEnumValue set = (SetEnumValue) kSubset.toSetEnum();
		assertEquals(496, set.size());
		Value[] array = set.elems.toArray();
		for (int i = 0; i < array.length; i++) {
			assertNotNull(array[i]);
			assertEquals(2, array[i].size());
		}
	}
	
	@Test
	public void testEnumerateN33() {
		final IntervalValue iv = new IntervalValue(1, 33);
		assertEquals(33, iv.size()); // Larger than Int/32 bits!

		final KSubsetValue kSubset = new KSubsetValue(2, iv);
		final SetEnumValue set = (SetEnumValue) kSubset.toSetEnum();
		assertEquals(528, set.size());
		Value[] array = set.elems.toArray();
		for (int i = 0; i < array.length; i++) {
			assertNotNull(array[i]);
			assertEquals(2, array[i].size());
		}
	}
	
	@Test
	public void testEnumerateN63() {
		final IntervalValue iv = new IntervalValue(1, 63);
		assertEquals(63, iv.size());

		final KSubsetValue kSubset = new KSubsetValue(2, iv);
		final SetEnumValue set = (SetEnumValue) kSubset.toSetEnum();
		assertEquals(1953, set.size());
		Value[] array = set.elems.toArray();
		for (int i = 0; i < array.length; i++) {
			assertNotNull(array[i]);
			assertEquals(2, array[i].size());
		}
	}
	
	@Test
	public void testEnumerateN64() {
		final IntervalValue iv = new IntervalValue(1, 64);
		assertEquals(64, iv.size());
		try {
			new KSubsetValue(42, iv).toSetEnum();
		} catch (IllegalArgumentException e) {
			return;
		}
		fail();
	}
	
	@Test
	public void testNormalization() {
		final ValueVec vals = new ValueVec();
		vals.addElement(IntValue.gen(1));
		vals.addElement(IntValue.gen(7));
		vals.addElement(IntValue.gen(42));
		vals.addElement(IntValue.gen(42));
		vals.addElement(IntValue.gen(23));
		final Value set = new SetEnumValue(vals, false);
		
		final KSubsetValue kSubset = new KSubsetValue(2, set);
		assertEquals(6, kSubset.size());
		
		final ValueEnumeration elements = kSubset.elements();
		assertEquals(new SetEnumValue(new Value[] { IntValue.gen(1), IntValue.gen(7) }, false), elements.nextElement());
		assertEquals(new SetEnumValue(new Value[] { IntValue.gen(1), IntValue.gen(23) }, false), elements.nextElement());
		assertEquals(new SetEnumValue(new Value[] { IntValue.gen(7), IntValue.gen(23) }, false), elements.nextElement());
		assertEquals(new SetEnumValue(new Value[] { IntValue.gen(1), IntValue.gen(42) }, false), elements.nextElement());
		assertEquals(new SetEnumValue(new Value[] { IntValue.gen(7), IntValue.gen(42) }, false), elements.nextElement());
		assertEquals(new SetEnumValue(new Value[] { IntValue.gen(23), IntValue.gen(42) }, false), elements.nextElement());
		assertNull(elements.nextElement());
	}

	private void doTest(final IntStream ints, final IntervalValue iv) {
		ints.forEach(i -> {
			final long expectedSize = Combinatorics.choose(iv.size(), i);

			final KSubsetValue kSubset = new KSubsetValue(i, iv);
			
			// Assert expected size before fingerprint and normalization.
			assertEquals(expectedSize, kSubset.size());
			
			// Check that fingerprint doesn't throw an exception.
			kSubset.fingerPrint(FP64.Zero);
			
			// Assert expected size after fingerprinting and normalization.
			assertEquals(expectedSize, kSubset.size());
			
			// Check if explicit enumeration of elements generates all elements.
			assertEquals(expectedSize, kSubset.toSetEnum().size());
		});
	}

	@Test
	public void testKSubsetFingerprintingS009() {
		doTest(IntStream.of(1, 9), new IntervalValue(1, 9));
	}

	@Test
	public void testKSubsetFingerprintingS032() {
		// In-between ks take too long, cause OOM or overflow exceptions.
		doTest(IntStream.of(1, 2, 3, 4, 5, 28, 29, 30, 31, 32), new IntervalValue(1, 32));
	}


	@Test
	public void testKSubsetFingerprintingS033() {
		// In-between ks take too long, cause OOM or overflow exceptions.
		doTest(IntStream.of(1, 2, 3, 4, 5, 29, 30, 31, 32, 33), new IntervalValue(1, 33));
	}

	@Test
	public void testKSubsetFingerprintingS063() {
		// In-between ks take too long, cause OOM or overflow exceptions.
		doTest(IntStream.of(1, 2, 3, 4, 60, 61, 62, 63), new IntervalValue(1, 63));
	}
}
/*

Assuming the definition of kSubset would be part of TLC, not the
CommunityModules, we would write a test for the following spec.

---- MODULE Github611 ----
EXTENDS FiniteSetsExt, FiniteSets, Naturals, TLC

ASSUME 50..150 \in kSubset(6, 1..200)

GenerateKSets ==
	kSubset(2, 1..63)

GenerateFilteredKSets ==
	{s \in GenerateKSets : Cardinality(s) = 2}

ASSUME GenerateKSets = GenerateFilteredKSets
 
S ==
	kSubset(2, 1..63)

VARIABLES a,b,c,d,e,f
vars == <<a,b,c,d,e,f>>

Init ==
	/\ a = kSubset(2, 1..63)
	/\ b = kSubset(4, 1..63)
	/\ c = kSubset(59, 1..63)
	/\ d = kSubset(61, 1..63)
	/\ e = S
	/\ f = GenerateFilteredKSets
	/\ PrintT(Cardinality(e))
	/\ PrintT(Cardinality(f))
	
Next ==
	UNCHANGED vars

Inv ==
	/\ Cardinality(a) = 1953 
	/\ Cardinality(b) = 595665 
	/\ Cardinality(c) = 595665 
	/\ Cardinality(d) = 1953 
	/\ Cardinality(e) = 1953
	/\ Cardinality(f) = 1953 

====

---- CONFIG Github611 ----
INIT Init
NEXT Next
INVARIANT Inv
====
*/