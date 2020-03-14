/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.BeforeClass;
import org.junit.Test;

import tlc2.util.FP64;
import util.InternTable;
import util.UniqueString;

public class InitializeValueTest {

	@BeforeClass
	public static void setup() {
		FP64.Init();
	}
	
	/**
	 * Test method for {@link tlc2.value.impl.UnionValue#deepNormalize()}.
	 */
	@Test
	public void union() {
		final ValueVec vec = new ValueVec();
		vec.addElement(new SetEnumValue(new IntValue[] {IntValue.gen(42)}, false));
		vec.addElement(new SetEnumValue(new IntValue[] {IntValue.gen(23)}, false));
		vec.addElement(new SetEnumValue(new IntValue[] {IntValue.gen(4711)}, false));
		vec.addElement(new SetEnumValue(new IntValue[] {IntValue.gen(1)}, false));
		
		final UnionValue uv = new UnionValue(new SetEnumValue(vec, false));
		assertFalse(uv.isNormalized());
		assertFalse(uv.set.isNormalized());
		
		uv.initialize();
		
		assertTrue(uv.set.isNormalized());
		assertTrue(uv.isNormalized());
	}

	/**
	 * Test method for {@link tlc2.value.impl.SetCapValue#deepNormalize()}.
	 */
	@Test
	public void setcap() {
		final ValueVec vec = new ValueVec();
		vec.addElement(IntValue.gen(42));
		vec.addElement(IntValue.gen(23));
		vec.addElement(IntValue.gen(4711));
		vec.addElement(IntValue.gen(1));
		
		SetCapValue scv = new SetCapValue(new SetEnumValue(vec, false), new SetEnumValue(vec, false));
		assertFalse(scv.isNormalized());
		assertFalse(scv.set1.isNormalized());
		assertFalse(scv.set2.isNormalized());
		
		scv.initialize();
		
		assertTrue(scv.set1.isNormalized());
		assertTrue(scv.set2.isNormalized());
		assertTrue(scv.isNormalized());
	}

	@Test
	public void setcup() {
		final ValueVec vec = new ValueVec();
		vec.addElement(IntValue.gen(42));
		vec.addElement(IntValue.gen(23));
		vec.addElement(IntValue.gen(4711));
		vec.addElement(IntValue.gen(1));
		
		SetCupValue scv = new SetCupValue(new SetEnumValue(vec, false), new SetEnumValue(vec, false));
		assertFalse(scv.isNormalized());
		assertFalse(scv.set1.isNormalized());
		assertFalse(scv.set2.isNormalized());
		
		scv.initialize();
		
		assertTrue(scv.set1.isNormalized());
		assertTrue(scv.set2.isNormalized());
		assertTrue(scv.isNormalized());
	}

	@Test
	public void setdiff() {
		final ValueVec vec = new ValueVec();
		vec.addElement(IntValue.gen(42));
		vec.addElement(IntValue.gen(23));
		vec.addElement(IntValue.gen(4711));
		vec.addElement(IntValue.gen(1));
		
		SetDiffValue sdv = new SetDiffValue(new SetEnumValue(vec, false), new SetEnumValue(vec, false));
		assertFalse(sdv.isNormalized());
		assertFalse(sdv.set1.isNormalized());
		assertFalse(sdv.set2.isNormalized());
		
		sdv.initialize();
		
		assertTrue(sdv.isNormalized());
		assertTrue(sdv.set1.isNormalized());
		assertTrue(sdv.set2.isNormalized());
	}

	@Test
	public void subset() {
		final ValueVec vec = new ValueVec();
		vec.addElement(IntValue.gen(42));
		vec.addElement(IntValue.gen(23));
		vec.addElement(IntValue.gen(4711));
		vec.addElement(IntValue.gen(1));
		
		SubsetValue sub = new SubsetValue(new SetEnumValue(vec, false));
		assertFalse(sub.isNormalized());
		assertFalse(sub.set.isNormalized());
		
		sub.initialize();
		
		assertTrue(sub.set.isNormalized());
		assertTrue(sub.isNormalized());
	}

	@Test
	public void record() {
		final InternTable internTable = new InternTable(2);
		final UniqueString a = internTable.put("a");
		final UniqueString b = internTable.put("b");
		
		final ValueVec vec = new ValueVec();
		vec.addElement(IntValue.gen(42));
		vec.addElement(IntValue.gen(23));
		vec.addElement(IntValue.gen(4711));
		vec.addElement(IntValue.gen(1));
		final Value aVal = new SetEnumValue(vec, false);
		final Value bVal = new SetEnumValue(vec, false);
		
		final RecordValue rcdv = new RecordValue(new UniqueString[] {b, a}, new Value[] {bVal, aVal}, false);

		assertFalse(rcdv.isNormalized());
		for (Value v : rcdv.values) {
			assertFalse(v.isNormalized());
		}
		
		rcdv.initialize();
		
		for (Value v : rcdv.values) {
			assertTrue(v.isNormalized());
		}
		assertTrue(rcdv.isNormalized());
	}

	@Test
	public void fcnrecord() {
		final ValueVec vec = new ValueVec();
		vec.addElement(IntValue.gen(42));
		vec.addElement(IntValue.gen(23));
		vec.addElement(IntValue.gen(4711));
		vec.addElement(IntValue.gen(1));
		final Value aVal = new SetEnumValue(vec, false);
		final Value bVal = new SetEnumValue(vec, false);

		final FcnRcdValue rcdv = new FcnRcdValue(new Value[] { new StringValue("B"), new StringValue("A") },
				new Value[] { bVal, aVal }, false);

		assertFalse(rcdv.isNormalized());
		for (Value v : rcdv.values) {
			assertFalse(v.isNormalized());
		}
		
		rcdv.initialize();
		
		for (Value v : rcdv.values) {
			assertTrue(v.isNormalized());
		}
		assertTrue(rcdv.isNormalized());
	}
	
	@Test
	public void tuple() {
		final ValueVec vec = new ValueVec();
		vec.addElement(IntValue.gen(42));
		vec.addElement(IntValue.gen(23));
		vec.addElement(IntValue.gen(4711));
		vec.addElement(IntValue.gen(1));
		final Value aVal = new SetEnumValue(vec, false);
		
		final TupleValue tuple = new TupleValue(aVal);

//		for (Value v : tuple.elems) {
//			assertFalse(v.isNormalized());
//		}
//		assertFalse(tuple.isNormalized());

		tuple.initialize();
		
		assertTrue(tuple.isNormalized());
		for (Value v : tuple.elems) {
			assertTrue(v.isNormalized());
		}
	}
	
	@Test
	public void setOfTuple() {
		final IntervalValue intVal = new IntervalValue(1, 2);
		final SetOfTuplesValue inner = new SetOfTuplesValue(intVal, intVal);
		final SetOfTuplesValue tuples = new SetOfTuplesValue(inner, inner);
		
//		for (Value v : tuples.sets) {
//			assertFalse(v.isNormalized());
//		}
//		assertFalse(tuples.isNormalized());
		
		tuples.initialize();
		
		assertTrue(tuples.isNormalized());
		for (Value v : tuples.sets) {
			assertTrue(v.isNormalized());
		}
	}
	
	@Test
	public void setOfRcds() {

		final Value[] values = new Value[3];
		values[0] = new SetEnumValue(getValue(7, "a"), true);
		values[1] = new IntervalValue(1, 2);
		values[2] = new IntervalValue(1, 4);

		final SetOfRcdsValue setOfRcrds= new SetOfRcdsValue(getNames(3), values, true);

//		for (Value v : setOfRcrds.values) {
//			assertFalse(v.isNormalized());
//		}
//		assertFalse(setOfRcrds.isNormalized());

		setOfRcrds.initialize();

		assertTrue(setOfRcrds.isNormalized());
		for (Value v : setOfRcrds.values) {
			assertTrue(v.isNormalized());
		}
	}

	private static final Value[] getValue(final int n, String str) {
		final Value[] values = new Value[n];
		for (int i = 0; i < n; i++) {
			values[i] = new StringValue(str + i);
		}
		return values;
	}

	private static final UniqueString[] getNames(final int n) {
		final UniqueString[] names = new UniqueString[n];
		for (int i = 0; i < names.length; i++) {
			names[i] = UniqueString.uniqueStringOf("N" + i);
		}
		return names;
	}
}
