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
package tlc2.value.impl;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.Set;

import org.junit.Test;

import tlc2.value.IValue;
import tlc2.value.RandomEnumerableValues;
import tlc2.value.impl.EnumerableValue.SubsetEnumerator;

public class EnumerableValueTest {

	@Test
	public void test() {
		RandomEnumerableValues.setSeed(15041980);
		
		final Set<Integer> indices = new HashSet<>();
		// For the first n \in Nat+ up to 10657 show that:
		for (int n = 1; n < 10657; n++) {
			final SubsetEnumerator enumerator = (SubsetEnumerator) new DummyValue(n).elements(n);

			while (enumerator.hasNext()) {
				final int index = enumerator.nextIndex();
				assertTrue("Index %s out of bounds.", 0 <= index && index < n);
				indices.add(index);
			}
			assertEquals("Missing indices.", n, indices.size());
			indices.clear();
		}
	}

	@SuppressWarnings("serial")
	class DummyValue extends EnumerableValue {

		private final int size;

		public DummyValue(int size) {
			this.size = size;
		}

		@Override
		public int size() {
			return size;
		}
		
		@Override
		public ValueEnumeration elements(final int k) {
			return new EnumerableValue.SubsetEnumerator(k) {
				@Override
				public Value nextElement() {
					return null;
				}
			};
		}

		@Override
		public ValueEnumeration elements() {
			return null;
		}

		@Override
		public byte getKind() {
			return 0;
		}

		@Override
		public int compareTo(Object val) {
			return 0;
		}

		@Override
		public boolean member(Value elem) {
			return false;
		}

		@Override
		public Value takeExcept(ValueExcept ex) {
			return null;
		}

		@Override
		public Value takeExcept(ValueExcept[] exs) {
			return null;
		}

		@Override
		public boolean isNormalized() {
			return false;
		}

		@Override
		public Value normalize() {
			return this;
		}

		@Override
		public boolean isFinite() {
			return false;
		}

		@Override
		public boolean isDefined() {
			return false;
		}

		@Override
		public IValue deepCopy() {
			return null;
		}

		@Override
		public boolean assignable(Value val) {
			return false;
		}

		@Override
		public StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
			return toString(sb, offset, swallow);
		}
	}
}
