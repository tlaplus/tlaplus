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

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.IntStream;

import org.junit.BeforeClass;
import org.junit.Test;

import tlc2.util.FP64;
import tlc2.value.impl.SetOfRcdsValue.SubsetEnumerator;
import util.UniqueString;

public class SetOfRcrdValueTest {

	private static final int a = 97;

	private static final Value[] getValue(final int n, String str) {
		final Value[] values = new Value[n];
		for (int i = 0; i < n; i++) {
			values[i] = new StringValue(str + i);
		}
		return values;
	}

	private static final Value[] getValue(int n, String... strs) {
		final Value[] values = new Value[strs.length];
		for (int i = 0; i < values.length; i++) {
			values[i] = new SetEnumValue(getValue(n, strs[i]), false);
		}
		return values;
	}

	private static final Value[] getValue(int n, UniqueString[] names) {
		// a,b,c,d,e,...
		return getValue(n, IntStream.range(a, a + names.length).mapToObj(ascii -> Character.toString((char) ascii))
				.toArray(String[]::new));
	}

	private static final UniqueString[] getNames(final int n) {
		final UniqueString[] names = new UniqueString[n];
		for (int i = 0; i < names.length; i++) {
			names[i] = UniqueString.uniqueStringOf("N" + i);
		}
		return names;
	}

	@BeforeClass
	public static void setup() {
		FP64.Init();
	}

	@Test
	public void testSimple() {
		final UniqueString[] names = getNames(3);
		
		final Value[] values = new Value[3];
		values[0] = new SetEnumValue(getValue(7, "a"), true);
		values[1] = new IntervalValue(1, 2);
		values[2] = new IntervalValue(1, 4);
		
		final SetOfRcdsValue setOfRcrdValue = new SetOfRcdsValue(names, values, true);

		checkElements(names, values, setOfRcrdValue, (SubsetEnumerator) setOfRcrdValue.elements(setOfRcrdValue.size()));
	}

	private static void checkElements(final UniqueString[] names, final Value[] values, final SetOfRcdsValue set,
			final SubsetEnumerator rcds) {
		for (int i = 0; i < set.size(); i++) {
			// Check names are stable.
			final RecordValue rcd = rcds.elementAt(i);
			assertArrayEquals(names, rcd.names);
			// Check values are from correct range.
			final Value[] rcdValues = rcd.values;
			for (int j = 0; j < rcdValues.length; j++) {
				assertTrue(values[j].member(rcdValues[j]));
			}
		}
	}
	
	@Test
	public void testRangeSubsetValue() {
		final UniqueString[] names = getNames(4);
		final SetOfRcdsValue setOfRcrdValue = new SetOfRcdsValue(names, getValue(2, names), true);

		final Set<Value> actual = new HashSet<>(setOfRcrdValue.elements(setOfRcrdValue.size()).all());
		assertEquals(setOfRcrdValue.size(), actual.size());

		final Set<Value> expected = new HashSet<>(setOfRcrdValue.elements().all());
		assertEquals(expected, actual);
	}

	@Test
	public void testRandomSubset() {
		final UniqueString[] names = getNames(4);
		final SetOfRcdsValue setOfRcrdValue = new SetOfRcdsValue(names, getValue(3, names), true);

		final int size = 27;
		final Enumerable randomSubset = setOfRcrdValue.getRandomSubset(size);
		final Set<RecordValue> randomsubsetValues = new HashSet<>(size);

		final ValueEnumeration enumerator = randomSubset.elements();
		RecordValue rcd;
		while ((rcd = (RecordValue) enumerator.nextElement()) != null) {
			assertEquals(names.length, rcd.names.length);
			assertEquals(names.length, rcd.values.length);
			randomsubsetValues.add(rcd);
			// Check element is in the original SetOfFcnsValue.
			assertTrue(setOfRcrdValue.member(rcd));
		}

		assertEquals(size, randomsubsetValues.size());
	}

	@Test
	public void testRandomSubsetVaryingParameters() {
		for (int n = 1; n < 7; n++) {
			final UniqueString[] names = getNames(n);
			for (int m = 1; m < 5; m++) {
				final SetOfRcdsValue setOfRcrdValue = new SetOfRcdsValue(names, getValue(m, names), true);
				final Set<RecordValue> randomsubsetValues = new HashSet<>();
				for (int kOutOfN = 0; kOutOfN < setOfRcrdValue.size(); kOutOfN++) {
					final Enumerable randomSubset = setOfRcrdValue.getRandomSubset(kOutOfN);

					final ValueEnumeration enumerator = randomSubset.elements();
					RecordValue rcd;
					while ((rcd = (RecordValue) enumerator.nextElement()) != null) {
						assertEquals(names.length, rcd.names.length);
						assertEquals(names.length, rcd.values.length);
						randomsubsetValues.add(rcd);
						// Check element is in the original SetOfFcnsValue.
						assertTrue(setOfRcrdValue.member(rcd));
					}

					assertEquals(kOutOfN, randomsubsetValues.size());
					randomsubsetValues.clear();
				}
			}
		}
	}

	@Test
	public void testRandomSubsetAstronomically() {
		//	RandomSubset(10000, [a1 : {k : k \in 1..50}, a2 : {k : k \in 1..50}, a3 : {k : k \in 1..50},
		//                       a4 : {k : k \in 1..50}, a5 : {k : k \in 1..50}, a6 : {k : k \in 1..50},
		//                       a7 : {k : k \in 1..50}, a8 : {k : k \in 1..50}, a9 : {k : k \in 1..50},
		//                      a10 : {k : k \in 1..50}])
		final UniqueString[] names = getNames(10);
		final SetOfRcdsValue setOfRcrdValue = new SetOfRcdsValue(names, getValue(50, names), true);

		final int k = 10000;
		final Enumerable randomSubset = setOfRcrdValue.getRandomSubset(k);
		final Set<RecordValue> randomsubsetValues = new HashSet<>(k);

		final ValueEnumeration enumerator = randomSubset.elements();
		RecordValue rcd;
		while ((rcd = (RecordValue) enumerator.nextElement()) != null) {
			assertEquals(names.length, rcd.names.length);
			assertEquals(names.length, rcd.values.length);
			randomsubsetValues.add(rcd);
			// Check element is in the original SetOfFcnsValue.
			assertTrue(setOfRcrdValue.member(rcd));
		}

		assertEquals(k, randomsubsetValues.size());
	}
}
