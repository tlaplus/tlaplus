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

import static org.junit.Assert.*;

import org.junit.Test;

import util.Assert.TLCRuntimeException;
import util.UniqueString;

public class ModelValueTest {
	
	// ------- #equals untyped MV ------- //

	@Test
	public void testEqualsUntyped() {
		ModelValue u1 = (ModelValue) ModelValue.make("u1");
		ModelValue u2 = (ModelValue) ModelValue.make("u2");
		
		assertNotEquals(u1, u2);
		assertNotEquals(u2, u1);
		assertEquals(u1, u1);
	}

	@Test
	public void testEqualsStringMV() {
		assertNotEquals(new StringValue("str"), ModelValue.make("untyped"));
		assertNotEquals(ModelValue.make("untyped"), new StringValue("str"));
	}
	
	@Test
	public void testEqualsIntMV() {
		assertNotEquals(IntValue.gen(0), ModelValue.make("untyped"));
		assertNotEquals(ModelValue.make("untyped"), IntValue.gen(0));
	}
	
	@Test
	public void testEqualsBoolMV() {
		assertNotEquals(BoolValue.ValFalse, ModelValue.make("untyped"));
		assertNotEquals(ModelValue.make("untyped"), BoolValue.ValFalse);
	}
	
	@Test
	public void testEqualsIVMV() {
		assertNotEquals(new IntervalValue(0, 1), ModelValue.make("untyped"));
		assertNotEquals(ModelValue.make("untyped"), new IntervalValue(0, 1));
	}
	
	@Test
	public void testEqualsRcdMV() {
		assertNotEquals(new RecordValue(UniqueString.of("foo"), new StringValue("bar")), ModelValue.make("untyped"));
		assertNotEquals(ModelValue.make("untyped"), new RecordValue(UniqueString.of("foo"), new StringValue("bar")));
	}
	
	@Test
	public void testEqualsTupeMV() {
		assertNotEquals(new TupleValue(new StringValue("foo")), ModelValue.make("untyped"));
		assertNotEquals(ModelValue.make("untyped"), new TupleValue(new StringValue("foo")));
	}
	
	// ------- #compareTo untyped MV ------- //

	@Test
	public void testCompareToUntyped() {
		ModelValue u1 = (ModelValue) ModelValue.make("u1");
		ModelValue u2 = (ModelValue) ModelValue.make("u2");
		
		assertEquals(-1, u1.compareTo(u2));
		assertEquals(1, u2.compareTo(u1));
		assertEquals(0, u1.compareTo(u1));
	}

	@Test
	public void testCompareToStringMV() {
		assertEquals(1, new StringValue("str").compareTo(ModelValue.make("untyped")));
		assertEquals(-1, ModelValue.make("untyped").compareTo(new StringValue("str")));
	}
	
	@Test
	public void testCompareToIntMV() {
		assertEquals(1, IntValue.gen(0).compareTo(ModelValue.make("untyped")));
		assertEquals(-1, ModelValue.make("untyped").compareTo(IntValue.gen(0)));
	}
	
	@Test
	public void testCompareToBoolMV() {
		assertEquals(1, BoolValue.ValFalse.compareTo(ModelValue.make("untyped")));
		assertEquals(-1, ModelValue.make("untyped").compareTo(BoolValue.ValFalse));
	}
	
	@Test
	public void testCompareToIVMV() {
		assertEquals(1, new IntervalValue(0, 1).compareTo(ModelValue.make("untyped")));
		assertEquals(-1, ModelValue.make("untyped").compareTo(new IntervalValue(0, 1)));
	}
	
	@Test
	public void testCompareToRcdMV() {
		assertEquals(1, new RecordValue(UniqueString.of("foo"), new StringValue("bar")).compareTo(ModelValue.make("untyped")));
		assertEquals(-1, ModelValue.make("untyped").compareTo(new RecordValue(UniqueString.of("foo"), new StringValue("bar"))));
	}
	
	@Test
	public void testCompareToTupeMV() {
		assertEquals(1, new StringValue("foo").compareTo(ModelValue.make("untyped")));
		assertEquals(-1, ModelValue.make("untyped").compareTo(new StringValue("foo")));
	}
	
	// ------- #equals typed MV ------- //
	
	@Test
	public void testEqualsTyped() {
		ModelValue a = (ModelValue) ModelValue.make("A_a");
		ModelValue b = (ModelValue) ModelValue.make("A_b");
		
		assertNotEquals(a,b);
		assertNotEquals(b,a);
		assertEquals(a, a);
	}

	@Test
	public void testEqualsTypedMVsUntyped() {
		assertNotEquals(ModelValue.make("A_a"), ModelValue.make("untyped"));
		assertNotEquals(ModelValue.make("untyped"), ModelValue.make("A_a"));
	}

	@Test(expected = TLCRuntimeException.class)
	public void testEqualsTwoTypedMVs() {
		ModelValue.make("A_a").equals(ModelValue.make("B_b"));
	}
	
	@Test(expected = TLCRuntimeException.class)
	public void testEqualsStringTypedMV() {
		new StringValue("str").equals(ModelValue.make("B_b"));
	}
	@Test(expected = TLCRuntimeException.class)
	public void testEqualsTypedMVString() {
		ModelValue.make("B_b").equals(new StringValue("str"));
	}
	
	@Test(expected = TLCRuntimeException.class)
	public void testEqualsIntTypedMV() {
		IntValue.gen(0).equals(ModelValue.make("B_b"));
	}
	@Test(expected = TLCRuntimeException.class)
	public void testEqualsTypedMVInt() {
		ModelValue.make("B_b").equals(IntValue.gen(0));
	}
	
	@Test(expected = TLCRuntimeException.class)
	public void testEqualsBoolTypedMV() {
		BoolValue.ValFalse.equals(ModelValue.make("B_b"));
	}
	@Test(expected = TLCRuntimeException.class)
	public void testEqualsTypedMVBool() {
		ModelValue.make("B_b").equals(BoolValue.ValTrue);
	}
	
	@Test(expected = TLCRuntimeException.class)
	public void testEqualsIVTypedMV() {
		new IntervalValue(0, 1).equals(ModelValue.make("B_b"));
	}
	@Test(expected = TLCRuntimeException.class)
	public void testEqualsTypedMVIV() {
		ModelValue.make("B_b").equals(new IntervalValue(0, 1));
	}
	
	@Test(expected = TLCRuntimeException.class)
	public void testEqualsRcdTypedMV() {
		new RecordValue(UniqueString.of("foo"), new StringValue("bar")).equals(ModelValue.make("B_b"));
	}
	@Test(expected = TLCRuntimeException.class)
	public void testEqualsTypedMVRcd() {
		ModelValue.make("B_b").equals(new RecordValue(UniqueString.of("foo"), new StringValue("bar")));
	}
	
	@Test(expected = TLCRuntimeException.class)
	public void testEqualsTupeTypedMV() {
		new TupleValue(new StringValue("foo")).equals(ModelValue.make("B_b"));
	}
	@Test(expected = TLCRuntimeException.class)
	public void testEqualsTypedMVTupe() {
		ModelValue.make("B_b").equals(new TupleValue(new StringValue("foo")));
	}

	// ------- #compareTo typed MV ------- //
	
	@Test
	public void testCompareToTyped() {
		ModelValue a = (ModelValue) ModelValue.make("A_a");
		ModelValue b = (ModelValue) ModelValue.make("A_b");
		
		assertEquals(-1, a.compareTo(b));
		assertEquals(1, b.compareTo(a));
		assertEquals(0, a.compareTo(a));
	}

	@Test
	public void testCompareToTypedMVsUntyped() {
		assertEquals(1, ModelValue.make("A_a").compareTo(ModelValue.make("untyped")));
		assertEquals(-1, ModelValue.make("untyped").compareTo(ModelValue.make("A_a")));
	}

	@Test(expected = TLCRuntimeException.class)
	public void testCompareToTwoTypedMVs() {
		ModelValue.make("A_a").compareTo(ModelValue.make("B_b"));
	}
	
	@Test(expected = TLCRuntimeException.class)
	public void testCompareToStringTypedMV() {
		new StringValue("str").compareTo(ModelValue.make("B_b"));
	}
	@Test(expected = TLCRuntimeException.class)
	public void testCompareToTypedMVString() {
		ModelValue.make("B_b").compareTo(new StringValue("str"));
	}
	
	@Test(expected = TLCRuntimeException.class)
	public void testCompareToIntTypedMV() {
		IntValue.gen(0).compareTo(ModelValue.make("B_b"));
	}
	@Test(expected = TLCRuntimeException.class)
	public void testCompareToTypedMVInt() {
		ModelValue.make("B_b").compareTo(IntValue.gen(0));
	}
	
	@Test(expected = TLCRuntimeException.class)
	public void testCompareToBoolTypedMV() {
		BoolValue.ValFalse.compareTo(ModelValue.make("B_b"));
	}
	@Test(expected = TLCRuntimeException.class)
	public void testCompareToTypedMVBool() {
		ModelValue.make("B_b").compareTo(BoolValue.ValTrue);
	}
	
	@Test(expected = TLCRuntimeException.class)
	public void testCompareToIVTypedMV() {
		new IntervalValue(0, 1).compareTo(ModelValue.make("B_b"));
	}
	@Test(expected = TLCRuntimeException.class)
	public void testCompareToTypedMVIV() {
		ModelValue.make("B_b").compareTo(new IntervalValue(0, 1));
	}
	
	@Test(expected = TLCRuntimeException.class)
	public void testCompareToRcdTypedMV() {
		new RecordValue(UniqueString.of("foo"), new StringValue("bar")).compareTo(ModelValue.make("B_b"));
	}
	@Test(expected = TLCRuntimeException.class)
	public void testCompareToTypedMVRcd() {
		ModelValue.make("B_b").compareTo(new RecordValue(UniqueString.of("foo"), new StringValue("bar")));
	}
	
	@Test(expected = TLCRuntimeException.class)
	public void testCompareToTupeTypedMV() {
		new TupleValue(new StringValue("foo")).compareTo(ModelValue.make("B_b"));
	}
	@Test(expected = TLCRuntimeException.class)
	public void testCompareToTypedMVTupe() {
		ModelValue.make("B_b").compareTo(new TupleValue(new StringValue("foo")));
	}
}
