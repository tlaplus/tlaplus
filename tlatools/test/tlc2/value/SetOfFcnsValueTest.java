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
 *   Ian Morris Nieves - added support for fingerprint stack trace
 ******************************************************************************/
package tlc2.value;

import static org.junit.Assert.*;

import org.junit.Test;

import tlc2.value.SetOfFcnsValue.SubsetEnumerator;

public class SetOfFcnsValueTest {

	private static final Value[] getValue(String... strs) {
		final Value[] values = new Value[strs.length];
		for (int i = 0; i < strs.length; i++) {
			values[i] = new StringValue(strs[i]);
		}
		return values;
	}

	@Test
	public void testRangeSubsetValue() {
		final Value[] values = new Value[] { ModelValue.make("m1"), ModelValue.make("m2"), ModelValue.make("m3") };
		final SetOfFcnsValue setOfFcnsValue = new SetOfFcnsValue(new SetEnumValue(values, true),
				new SubsetValue(new SetEnumValue(
						new Value[] { new StringValue("a"), new StringValue("b"), new StringValue("c") }, true)));

		assertEquals(512, setOfFcnsValue.size());

		final SetOfFcnsValue.SubsetEnumerator enumerator = (SubsetEnumerator) setOfFcnsValue.elements(1d);
		final SetEnumValue emptyset = new SetEnumValue();
		int i = 0;
		assertEquals(new FcnRcdValue(values, new Value[] { emptyset, emptyset, emptyset }, true),
				enumerator.elementAt(i++));
		assertEquals(
				new FcnRcdValue(values,
						new Value[] { emptyset, emptyset,
								new SetEnumValue(new Value[] { new StringValue("a") }, true) },
						true),
				enumerator.elementAt(i++));
		assertEquals(
				new FcnRcdValue(values,
						new Value[] { emptyset, emptyset,
								new SetEnumValue(new Value[] { new StringValue("b") }, true) },
						true),
				enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(values,
				new Value[] { emptyset, emptyset,
						new SetEnumValue(new Value[] { new StringValue("a"), new StringValue("b") }, true) },
				true), enumerator.elementAt(i++));
		assertEquals(
				new FcnRcdValue(values,
						new Value[] { emptyset, emptyset,
								new SetEnumValue(new Value[] { new StringValue("c") }, true) },
						true),
				enumerator.elementAt(i++));

		// Last element
		final SetEnumValue setEnumValue = new SetEnumValue(
				new Value[] { new StringValue("a"), new StringValue("b"), new StringValue("c") }, true);
		assertEquals(new FcnRcdValue(values, new Value[] { setEnumValue, setEnumValue, setEnumValue }, true),
				enumerator.elementAt(511));
	}

	@Test
	public void testDomainModelValue() {
		final Value[] domain = new Value[] { ModelValue.make("m1"), ModelValue.make("m2"), ModelValue.make("m3") };
		final SetOfFcnsValue setOfFcnsValue = new SetOfFcnsValue(new SetEnumValue(domain, true),
				new SetEnumValue(getValue("a", "b", "c"), true));

		assertEquals(27, setOfFcnsValue.size());

		final SetOfFcnsValue.SubsetEnumerator enumerator = (SubsetEnumerator) setOfFcnsValue.elements(1d);
		for (int i = 0; i < setOfFcnsValue.size(); i++) {
			FcnRcdValue rcd = (FcnRcdValue) enumerator.elementAt(i);
			assertEquals(3, rcd.domain.length);
			assertEquals(3, rcd.values.length);
		}

		int i = 0;
		assertEquals(new FcnRcdValue(domain, getValue("a", "a", "a"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "a", "b"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "a", "c"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "b", "a"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "b", "b"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "b", "c"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "c", "a"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "c", "b"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "c", "c"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "a", "a"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "a", "b"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "a", "c"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "b", "a"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "b", "b"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "b", "c"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "c", "a"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "c", "b"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "c", "c"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "a", "a"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "a", "b"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "a", "c"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "b", "a"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "b", "b"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "b", "c"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "c", "a"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "c", "b"), true), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "c", "c"), true), enumerator.elementAt(i++));
	}

	@Test
	public void testDomainIntervalRangeSetEnumValueSize9() {
		final IntervalValue domain = new IntervalValue(1, 2);
		final SetOfFcnsValue setOfFcnsValue = new SetOfFcnsValue(domain,
				new SetEnumValue(getValue("a", "b", "c"), true));

		assertEquals(9, setOfFcnsValue.size());

		final SetOfFcnsValue.SubsetEnumerator enumerator = (SubsetEnumerator) setOfFcnsValue.elements(1d);
		for (int i = 0; i < setOfFcnsValue.size(); i++) {
			FcnRcdValue rcd = (FcnRcdValue) enumerator.elementAt(i);
			assertEquals(2, rcd.domain.length);
			assertEquals(2, rcd.values.length);
		}

		int i = 0;
		assertEquals(new FcnRcdValue(domain, getValue("a", "a")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "b")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "c")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "a")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "b")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "c")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "a")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "b")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "c")), enumerator.elementAt(i++));
	}

	@Test
	public void testDomainIntervalRangeSetEnumValueSize27() {
		final IntervalValue domain = new IntervalValue(1, 3);
		final SetOfFcnsValue setOfFcnsValue = new SetOfFcnsValue(domain,
				new SetEnumValue(getValue("a", "b", "c"), true));

		assertEquals(27, setOfFcnsValue.size());

		final SetOfFcnsValue.SubsetEnumerator enumerator = (SubsetEnumerator) setOfFcnsValue.elements(1d);
		for (int i = 0; i < setOfFcnsValue.size(); i++) {
			FcnRcdValue rcd = (FcnRcdValue) enumerator.elementAt(i);
			assertEquals(3, rcd.domain.length);
			assertEquals(3, rcd.values.length);
		}

		int i = 0;
		assertEquals(new FcnRcdValue(domain, getValue("a", "a", "a")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "a", "b")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "a", "c")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "b", "a")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "b", "b")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "b", "c")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "c", "a")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "c", "b")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "c", "c")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "a", "a")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "a", "b")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "a", "c")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "b", "a")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "b", "b")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "b", "c")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "c", "a")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "c", "b")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("b", "c", "c")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "a", "a")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "a", "b")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "a", "c")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "b", "a")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "b", "b")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "b", "c")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "c", "a")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "c", "b")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("c", "c", "c")), enumerator.elementAt(i++));
	}

	@Test
	public void testDomainIntervalRangeSetEnumValueSize256() {
		final IntervalValue domain = new IntervalValue(1, 4);
		final SetOfFcnsValue setOfFcnsValue = new SetOfFcnsValue(domain,
				new SetEnumValue(getValue("a", "b", "c", "d"), true));

		assertEquals(256, setOfFcnsValue.size());

		final SetOfFcnsValue.SubsetEnumerator enumerator = (SubsetEnumerator) setOfFcnsValue.elements(1d);
		for (int i = 0; i < setOfFcnsValue.size(); i++) {
			FcnRcdValue rcd = (FcnRcdValue) enumerator.elementAt(i);
			assertEquals(4, rcd.domain.length);
			assertEquals(4, rcd.values.length);
		}

		int i = 0;
		assertEquals(new FcnRcdValue(domain, getValue("a", "a", "a", "a")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "a", "a", "b")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "a", "a", "c")), enumerator.elementAt(i++));
		assertEquals(new FcnRcdValue(domain, getValue("a", "a", "a", "d")), enumerator.elementAt(i++));
		// ... (to lazy to type them out)
		assertEquals(new FcnRcdValue(domain, getValue("d", "d", "d", "b")), enumerator.elementAt(253));
		assertEquals(new FcnRcdValue(domain, getValue("d", "d", "d", "c")), enumerator.elementAt(254));
		assertEquals(new FcnRcdValue(domain, getValue("d", "d", "d", "d")), enumerator.elementAt(255));
	}
}
