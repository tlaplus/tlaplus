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
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import org.junit.BeforeClass;
import org.junit.Test;

import tlc2.util.FP64;
import tlc2.value.RandomEnumerableValues;
import tlc2.value.impl.Enumerable.Ordering;
import tlc2.value.impl.SubsetValue.CoinTossingSubsetEnumerator;
import tlc2.value.impl.SubsetValue.KElementEnumerator;
import tlc2.value.impl.SubsetValue.SubsetEnumerator;
import tlc2.value.impl.SubsetValue.Unrank;
import util.Assert;

public class SubsetValueTest {

	private static final Value[] getValue(String... strs) {
		final List<Value> values = new ArrayList<>(strs.length);
		for (int i = 0; i < strs.length; i++) {
			values.add(new StringValue(strs[i]));
		}
		Collections.shuffle(values);
		return values.toArray(new Value[values.size()]);
	}

	@BeforeClass
	public static void setup() {
		// Make test repeatable by setting random seed always to same value. 
		RandomEnumerableValues.setSeed(15041980L);
		// Needed to insert elements into java.util.Set (because of hashcode) later to
		// detect duplicates.
		FP64.Init();
	}

	private void doTest(final int expectedSize, final EnumerableValue innerSet) {
		doTest(expectedSize, innerSet, expectedSize);
	}

	private void doTest(final int expectedSize, final EnumerableValue innerSet,
			int expectedElements) {
		final SubsetValue subsetValue = new SubsetValue(innerSet);
		assertEquals(expectedSize, subsetValue.size());

		final Set<Value> s = new TreeSet<>(new Comparator<Value>() {
			@Override
			public int compare(Value o1, Value o2) {
				// o1.normalize();
				// ((SetEnumValue) o1).elems.sort(true);
				//
				// o2.normalize();
				// ((SetEnumValue) o2).elems.sort(true);

				return o1.compareTo(o2);
			}
		});
		
		final ValueEnumeration elements = subsetValue.elements(expectedElements);
		assertTrue(elements instanceof SubsetEnumerator);
		
		SetEnumValue next = null;
		while ((next = (SetEnumValue) elements.nextElement()) != null) {
			final int size = next.elems.size();
			assertTrue(0 <= size && size <= innerSet.size());
			s.add(next);
		}
		assertEquals(expectedElements, s.size());
	}

	@Test
	public void testRandomSubsetE7F1() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d", "e", "f", "g"), true);
		doTest(1 << innerSet.size(), innerSet);
	}

	@Test
	public void testRandomSubsetE7F05() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d", "e", "f", "g"), true);
		doTest(1 << innerSet.size(), innerSet, 64);
	}

	@Test
	public void testRandomSubsetE6F1() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d", "e", "f"), true);
		doTest(1 << innerSet.size(), innerSet);
	}

	@Test
	public void testRandomSubsetE5F01() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d", "e"), true);
		doTest(1 << innerSet.size(), innerSet, 4);
	}

	@Test
	public void testRandomSubsetE5F025() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d", "e"), true);
		doTest(1 << innerSet.size(), innerSet, 8);
	}

	@Test
	public void testRandomSubsetE5F05() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d", "e"), true);
		doTest(1 << innerSet.size(), innerSet, 16);
	}

	@Test
	public void testRandomSubsetE5F075() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d", "e"), true);
		doTest(1 << innerSet.size(), innerSet, 24);
	}

	@Test
	public void testRandomSubsetE5F1() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d", "e"), true);
		doTest(1 << innerSet.size(), innerSet);
	}

	@Test
	public void testRandomSubsetE32F1ENeg6() {
		final IntervalValue innerSet = new IntervalValue(1, 32);
		final SubsetValue subsetValue = new SubsetValue(innerSet);

		ValueEnumeration elements = subsetValue.elements(2342);
		assertTrue(elements instanceof CoinTossingSubsetEnumerator);

		final Set<Value> s = new HashSet<>();
		SetEnumValue next = null;
		while ((next = (SetEnumValue) elements.nextElement()) != null) {
			final int size = next.elems.size();
			assertTrue(0 <= size && size <= innerSet.size());
			s.add(next);
		}

		CoinTossingSubsetEnumerator tossingEnumerator = (CoinTossingSubsetEnumerator) elements;
		assertTrue(tossingEnumerator.getNumOfPicks() - 100 <= s.size() && s.size() <= tossingEnumerator.getNumOfPicks());
	}

	@Test
	public void testRandomSubsetE17F1ENeg3() {
		final IntervalValue innerSet = new IntervalValue(1, 17);
		final SubsetValue subsetValue = new SubsetValue(innerSet);

		final ValueEnumeration elements = subsetValue.elements(4223);
		assertTrue(elements instanceof SubsetEnumerator);

		final Set<Value> s = new HashSet<>();
		SetEnumValue next = null;
		while ((next = (SetEnumValue) elements.nextElement()) != null) {
			final int size = next.elems.size();
			assertTrue(0 <= size && size <= innerSet.size());
			s.add(next);
		}

		final SubsetEnumerator enumerator = (SubsetEnumerator) elements;
		assertEquals(enumerator.k, s.size());
	}

	@Test
	public void testRandomSubsetSubset16() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b"), true);
		final SubsetValue innerSubset = new SubsetValue(innerSet);
		final SubsetValue subsetValue = new SubsetValue(innerSubset);

		final int expectedSize = 1 << innerSubset.size();
		assertEquals(expectedSize, subsetValue.size());

		// No duplicates
		final Set<Value> s = new HashSet<>(expectedSize);
		final ValueEnumeration elements = subsetValue.elements(expectedSize);
		Value next = null;
		while ((next = elements.nextElement()) != null) {
			s.add(next);
		}
		assertEquals(expectedSize, s.size());
	}

	@Test
	public void testRandomSubsetSubset256() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c"), true);
		final SubsetValue innerSubset = new SubsetValue(innerSet);
		final SubsetValue subsetValue = new SubsetValue(innerSubset);

		final int expectedSize = 1 << innerSubset.size();
		assertEquals(expectedSize, subsetValue.size());

		// No duplicates
		final Set<Value> s = new HashSet<>(expectedSize);
		final ValueEnumeration elements = subsetValue.elements(expectedSize);
		Value next = null;
		while ((next = elements.nextElement()) != null) {
			s.add(next);
		}
		assertEquals(expectedSize, s.size());
	}

	@Test
	public void testRandomSubsetSubset65536() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d"), true);
		final SubsetValue innerSubset = new SubsetValue(innerSet);
		final SubsetValue subsetValue = new SubsetValue(innerSubset);

		final int expectedSize = 1 << innerSubset.size();
		assertEquals(expectedSize, subsetValue.size());

		// No duplicates
		final Set<Value> s = new HashSet<>(expectedSize);
		final ValueEnumeration elements = subsetValue.elements(expectedSize);
		Value next = null;
		while ((next = elements.nextElement()) != null) {
			s.add(next);
		}
		assertEquals(expectedSize, s.size());
	}

	@Test
	public void testRandomSubsetSubsetNoOverflow() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d", "e"), true);
		final SubsetValue innerSubset = new SubsetValue(innerSet);
		final SubsetValue subsetValue = new SubsetValue(innerSubset);

		try {
			subsetValue.size();
		} catch (Assert.TLCRuntimeException e) {
			final Set<Value> s = new HashSet<>();

			final ValueEnumeration elements = subsetValue.elements(2148);
			assertTrue(elements instanceof CoinTossingSubsetEnumerator);
			Value next = null;
			while ((next = elements.nextElement()) != null) {
				s.add(next);
			}
			// No duplicates
			assertEquals(2148, s.size());
		}
	}
	
	@Test
	public void testKSubsetEnumerator() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d"), true);
		final SubsetValue subset = new SubsetValue(innerSet);
		
		assertEquals(1, subset.numberOfKElements(0));
		assertEquals(4, subset.numberOfKElements(1));
		assertEquals(6, subset.numberOfKElements(2));
		assertEquals(4, subset.numberOfKElements(3));
		assertEquals(1, subset.numberOfKElements(4));

		ValueEnumeration enumerator = subset.kElements(0);
		assertEquals(new SetEnumValue(), enumerator.nextElement());
		assertNull(enumerator.nextElement());
		
		// Need to sort KElementEnumerator to be able to predict the order in which
		// elements get returned.
		enumerator = ((KElementEnumerator) subset.kElements(1)).sort();
		assertEquals(new SetEnumValue(getValue("a"), false), enumerator.nextElement());
		assertEquals(new SetEnumValue(getValue("b"), false), enumerator.nextElement());
		assertEquals(new SetEnumValue(getValue("c"), false), enumerator.nextElement());
		assertEquals(new SetEnumValue(getValue("d"), false), enumerator.nextElement());
		assertNull(enumerator.nextElement());
		
		enumerator = ((KElementEnumerator) subset.kElements(2)).sort();
		assertEquals(new SetEnumValue(getValue("a", "b"), false), enumerator.nextElement());
		assertEquals(new SetEnumValue(getValue("a", "c"), false), enumerator.nextElement());
		assertEquals(new SetEnumValue(getValue("b", "c"), false), enumerator.nextElement());
		assertEquals(new SetEnumValue(getValue("a", "d"), false), enumerator.nextElement());
		assertEquals(new SetEnumValue(getValue("b", "d"), false), enumerator.nextElement());
		assertEquals(new SetEnumValue(getValue("c", "d"), false), enumerator.nextElement());
		assertNull(enumerator.nextElement());

		enumerator = ((KElementEnumerator) subset.kElements(3)).sort();
		assertEquals(new SetEnumValue(getValue("a", "b", "c"), false), enumerator.nextElement());
		assertEquals(new SetEnumValue(getValue("a", "b", "d"), false), enumerator.nextElement());
		assertEquals(new SetEnumValue(getValue("a", "c", "d"), false), enumerator.nextElement());
		assertEquals(new SetEnumValue(getValue("b", "c", "d"), false), enumerator.nextElement());
		assertNull(enumerator.nextElement());
		
		enumerator = ((KElementEnumerator) subset.kElements(4)).sort();
		assertEquals(new SetEnumValue(getValue("a", "b", "c", "d"), false), enumerator.nextElement());
		assertNull(enumerator.nextElement());
	}
	
	@Test
	public void testKSubsetEnumeratorNegative() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d"), true);
		final SubsetValue subset = new SubsetValue(innerSet);
		try {
			subset.kElements(-1);
		} catch (IllegalArgumentException e) {
			return;
		}
		fail();
	}
	
	@Test
	public void testKSubsetEnumeratorGTCapacity() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d"), true);
		final SubsetValue subset = new SubsetValue(innerSet);
		try {
			subset.kElements(innerSet.size() + 1);
		} catch (IllegalArgumentException e) {
			return;
		}
		fail();
	}
	
	@Test
	public void testNumKSubset() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d", "e"), true);
		final SubsetValue subset = new SubsetValue(innerSet);

		assertEquals(1, subset.numberOfKElements(0));
		assertEquals(5, subset.numberOfKElements(1));
		assertEquals(10, subset.numberOfKElements(2));
		assertEquals(10, subset.numberOfKElements(3));
		assertEquals(5, subset.numberOfKElements(4));
		assertEquals(1, subset.numberOfKElements(5));
	}

	@Test
	public void testNumKSubset2() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d", "e", "f", "g", "h"), true);
		final SubsetValue subset = new SubsetValue(innerSet);

		int sum = 0;
		for (int i = 0; i <= innerSet.size(); i++) {
			sum += subset.numberOfKElements(i);
		}
		assertEquals(1 << innerSet.size(), sum);
	}
	
	@Test
	public void testNumKSubsetNeg() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d", "e"), true);
		final SubsetValue subset = new SubsetValue(innerSet);

		try {
			subset.numberOfKElements(-1);
		} catch (IllegalArgumentException e) {
			return;
		}
		fail();
	}
	
	@Test
	public void testNumKSubsetKGTN() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d", "e"), true);
		final SubsetValue subset = new SubsetValue(innerSet);

		try {
			subset.numberOfKElements(innerSet.size() + 1);
		} catch (IllegalArgumentException e) {
			return;
		}
		fail();
	}
	
	@Test
	public void testNumKSubsetUpTo62() {
		for (int i = 1; i < 62; i++) {
			final SubsetValue subset = new SubsetValue(new IntervalValue(1, i));
			long sum = 0L;
			for (int j = 0; j <= i; j++) {
				sum += subset.numberOfKElements(j);
			}
			assertEquals(1L << i, sum);
		}
	}
	
	@Test
	public void testNumKSubsetPreventsOverflow() {
		final IntervalValue innerSet = new IntervalValue(1, 64);
		final SubsetValue subset = new SubsetValue(innerSet);
		for (int i = 0; i <= innerSet.size(); i++) {
			try {
				subset.numberOfKElements(i);
			} catch (IllegalArgumentException e) {
				continue;
			}
			fail();
		}
	}
	
	@Test
	public void testUnrankKSubsets() {
		final SetEnumValue innerSet = new SetEnumValue(getValue("a", "b", "c", "d", "e"), true);
		final SubsetValue subset = new SubsetValue(innerSet);
		
		final int sizeS = innerSet.size();
		for (int k = 0; k < sizeS; k++) {
			final Unrank unranker = subset.getUnrank(k);
			// for each k-subset...
			final long numElementsInKSubset = subset.numberOfKElements(k);
			final Set<Value> kSubset = new HashSet<>();
			for (int i = 0; i < numElementsInKSubset; i++) {
				final Value kElementAt = unranker.subsetAt(i);
				// check k-Subset is indeed k-Subset
				assertEquals(k, kElementAt.size());
				kSubset.add(kElementAt);
			}
			// check for no duplicates.
			assertEquals(numElementsInKSubset, kSubset.size());
		}
	}

	@Test
	public void testUnrank16viaRank() {
		final IntervalValue innerSet = new IntervalValue(1, 16);
		final SubsetValue subset = new SubsetValue(innerSet);
		
		int size = innerSet.size();
		
		final long sizeS = 1L << size; // 2^innerSet.size()
		final Set<Value> unranked = new HashSet<>((int)sizeS);
		
		for (int k = 0; k <= size; k++) {
			final Unrank unranker = subset.getUnrank(k);
			// for each k-subset...
			final long numElementsInKSubset = subset.numberOfKElements(k);
			for (int i = 0; i < numElementsInKSubset; i++) {
				final Value kElementAt = unranker.subsetAt(i);
				assertEquals(k, kElementAt.size());
				unranked.add(kElementAt);
			}
		}
		assertEquals(sizeS, unranked.size());
	}

	@Test
	public void testRandomSetOfSubsets() {
		final IntervalValue innerSet = new IntervalValue(1, 22);
		final SubsetValue subset = new SubsetValue(innerSet);
		
		final int maxLength = 10;
		final int k = 23131;
		final SetEnumValue setOfSubsets = (SetEnumValue) subset.getRandomSetOfSubsets(k, maxLength);
		assertEquals(k, setOfSubsets.size());
		
		final ValueEnumeration elements = setOfSubsets.elements();
		Value val = null;
		while ((val = elements.nextElement()) != null) {
			assertTrue(val.size() <= maxLength);
		}
		setOfSubsets.normalize();
		assertEquals(k, setOfSubsets.size());
	}

	@Test
	public void testRandomSetOfSubsets300() {
		final IntervalValue innerSet = new IntervalValue(1, 300);
		final SubsetValue subset = new SubsetValue(innerSet);
		
		final int maxLength = 9;
		final int k = 23071;
		final SetEnumValue setOfSubsets = (SetEnumValue) subset.getRandomSetOfSubsets(k, maxLength);
		assertEquals(k, setOfSubsets.size());
		
		final ValueEnumeration elements = setOfSubsets.elements();
		Value val = null;
		while ((val = elements.nextElement()) != null) {
			assertTrue(val.size() <= maxLength);
		}
		setOfSubsets.normalize();
		assertEquals(k, setOfSubsets.size());
	}

	@Test
	public void testRandomSetOfSubsets400() {
		final IntervalValue innerSet = new IntervalValue(1, 400);
		final SubsetValue subset = new SubsetValue(innerSet);
		
		final int maxLength = 9;
		final int k = 23077;
		final SetEnumValue setOfSubsets = (SetEnumValue) subset.getRandomSetOfSubsets(k, maxLength);
		assertEquals(k, setOfSubsets.size());
		
		final ValueEnumeration elements = setOfSubsets.elements();
		Value val = null;
		while ((val = elements.nextElement()) != null) {
			assertTrue(val.size() <= maxLength);
		}
		setOfSubsets.normalize();
		assertEquals(k, setOfSubsets.size());
	}
	
	@Test
	public void testSubsetNeedsNormalization() {
		final IntervalValue inner = new IntervalValue(1, 5);
		final SubsetValue subset = new SubsetValue(inner);

		final ValueVec vec = new ValueVec(subset.size());
		for (int i = 0; i <= inner.size(); i++) {
			List<Value> kElements = subset.kElements(i).all();
			kElements.forEach(e -> vec.addElement(e));
		}
        final Value unnormalized = new SetEnumValue(vec, false);
        
        final Value normalized = subset.toSetEnum().normalize();
        
        assertEquals(normalized, unnormalized);
	}
	
	@Test
	public void testSubsetNeedsNormalization2() {
		final IntervalValue inner = new IntervalValue(1, 6);
		final SubsetValue subset = new SubsetValue(inner);

		final ValueVec vec = new ValueVec(subset.size());
		final ValueEnumeration bElements = subset.elementsNormalized();
		bElements.forEach(e -> vec.addElement(e));
        final Value unnormalized = new SetEnumValue(vec, true);
        
        final Value normalized = subset.toSetEnum().normalize();
        
        assertEquals(normalized, unnormalized);
	}

	@Test
	public void testRandomSubsetGeneratorK0() {
		final Set<Value> values = new HashSet<>();
		final SubsetValue subsetValue = new KSubsetValue(0, new IntervalValue(1, 10));
		final ValueEnumeration elements = subsetValue.elements(Ordering.RANDOMIZED);
		for (int i = 0; i < 100; i++) {
			final Value nextElement = elements.nextElement();
			values.add(nextElement);
		}
		assertEquals(1, values.size()); //empty set
	}
	
	@Test
	public void testRandomSubsetGeneratorKNegative() {
		try {
			new KSubsetValue(-1, new IntervalValue(1, 2)).elements(Ordering.RANDOMIZED);
		} catch (IllegalArgumentException e) {
			return;
		}
		fail("Expected an IllegalArgumentException");
	}
	
	@Test
	public void testRandomSubsetGeneratorKNplus1() {
		try {
			new KSubsetValue(3, new IntervalValue(1, 2)).elements(Ordering.RANDOMIZED);
		} catch (IllegalArgumentException e) {
			return;
		}
		fail("Expected an IllegalArgumentException");
	}
	
	@Test
	public void testRandomSubsetGeneratorN10() {
		final Set<Value> values = new HashSet<>();
		final SubsetValue subsetValue = new KSubsetValue(3, new IntervalValue(1, 10));
		final ValueEnumeration elements = subsetValue.elements(Ordering.RANDOMIZED);
		for (int i = 0; i < 1000; i++) {
			final Value nextElement = elements.nextElement();
			values.add(nextElement);
		}
		// Eventually, the impl generates all values with high probability.
		assertEquals(subsetValue.numberOfKElements(3), values.size());
	}

	// N100 would overflow default implementation in SubsetValue.
	@Test
	public void testRandomSubsetGeneratorN100() {
		final Set<Value> values = new HashSet<>();
		final SubsetValue subsetValue = new KSubsetValue(3, new IntervalValue(1, 100));
		final ValueEnumeration elements = subsetValue.elements(Ordering.RANDOMIZED);
		for (int i = 0; i < 100; i++) {
			final Value nextElement = elements.nextElement();
			values.add(nextElement);
		}
		// For large input sets, generating a small number of subsets doesn't cause
		// significant duplicates.
		assertEquals(100, values.size());
	}
}

/*

A spec by Jack Vanlightly as an eyeball test to empirically measures the distributions. 

---- CONFIG ksubsets_ex_quant ----
SPECIFICATION Spec
=====

------------------------------ MODULE ksubsets_ex_quant ------------------------------
EXTENDS Naturals, Randomization, FiniteSets, TLC, FiniteSetsExt

Elements == 1..500
Limit == 1000

VARIABLES counts,
          total

vars == <<counts, total >>

AddSubset ==
    /\ total < Limit 
    \* /\ \E ss \in SUBSET Elements : 
    \*     /\ Cardinality(ss) = 3 
    /\ \E ss \in kSubset(3, Elements) : 
        /\ IF ss \in DOMAIN counts
            THEN counts' = [counts EXCEPT ![ss] = @ + 1]
            ELSE counts' = counts @@ (ss :> 1)
        /\ total' = total + 1

PrintDist ==
    /\ total = Limit
    /\ total' = Limit + 1
    /\ UNCHANGED <<counts>>
    /\ \A ss \in DOMAIN counts : PrintT(<<total, ss, counts[ss]>>)
    /\ PrintT(<<"RESULT", Cardinality(DOMAIN counts)>>)

Init == 
    /\ counts = [ss \in {} |-> 0]
    /\ total = 0

Next ==
    \/ AddSubset
    \/ PrintDist

Spec == Init /\ [][Next]_vars  

=============================================================================
\* Modification History
\* Last modified Wed Oct 28 09:08:31 PDT 2020 by markus
\* Last modified Tue Oct 27 17:24:00 CET 2020 by jvanlightly
\* Created Tue Oct 27 09:55:35 CET 2020 by jvanlightly
*/
