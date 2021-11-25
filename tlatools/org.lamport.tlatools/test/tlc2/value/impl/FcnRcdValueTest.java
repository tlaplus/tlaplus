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

import java.util.ArrayList;
import java.util.List;

import org.junit.BeforeClass;
import org.junit.Test;

import tlc2.util.FP64;
import tlc2.value.RandomEnumerableValues;

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
}
