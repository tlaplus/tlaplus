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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.junit.BeforeClass;
import org.junit.Test;

import tlc2.util.FP64;
import tlc2.value.RandomEnumerableValues;

public class FcnRcdValueTest {

	private static final Value[] getValue(String... strs) {
		final List<Value> values = new ArrayList<>(strs.length);
		for (int i = 0; i < strs.length; i++) {
			values.add(new StringValue(strs[i]));
		}
		Collections.shuffle(values);
		return values.toArray(new Value[values.size()]);
	}
	
	private static final Value[] getInts(int n, int offset) {
		Value[] res = new Value[n];
		for (int i = 0; i < n; i++) {
			res[i] = IntValue.gen(offset + i);
		}
		return res;
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
	public void testSelect() {
		for (int i = 0; i < 64; i++) {
			Value[] dom = getInts(i, 0);
			Value[] rng = getInts(i, i);
			FcnRcdValue rcdValue = new FcnRcdValue(dom, rng, false);
			for (int j = 0; j < dom.length; j++) {
				IntValue val = (IntValue) rcdValue.select(dom[j]);
				assertNotNull(val);
				assertEquals(j + i, val.val);
			}
		}
	}

	@Test
	public void testSelectNormalized() {
		for (int i = 0; i < 64; i++) {
			Value[] dom = getInts(i, 0);
			Value[] rng = getInts(i, i);
			FcnRcdValue rcdValue = (FcnRcdValue) new FcnRcdValue(dom, rng, false).normalize();
			for (int j = 0; j < dom.length; j++) {
				IntValue val = (IntValue) rcdValue.select(dom[j]);
				assertNotNull(val);
				assertEquals(j + i, val.val);
			}
		}
	}
}
