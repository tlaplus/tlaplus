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

import java.math.BigInteger;

import tlc2.value.RandomEnumerableValues;

public abstract class SetOfFcnsOrRcdsValue extends EnumerableValue {

	@Override
	public EnumerableValue getRandomSubset(final int kOutOfN) {
		final ValueVec vec = new ValueVec(kOutOfN);

		final ValueEnumeration ve = elements(kOutOfN);

		Value v = null;
		while ((v = ve.nextElement()) != null) {
			vec.addElement(v);
		}
    	
		// Assert no duplicates. For large sets we assume kOutOfN < size() to avoid
		// calling size() which then throws an assertion exception anyway.
		assert (needBigInteger() ? vec.sort(true).size() == kOutOfN
				: vec.sort(true).size() == Math.min(kOutOfN, size()));

		if (coverage) {cm.incSecondary(vec.size());}
    	return new SetEnumValue(vec, false, cm);
	}

	@Override
	public ValueEnumeration elements(final int k) {
		if (needBigInteger()) {
			return getBigSubsetEnumerator(k);
		} else {
			return getSubsetEnumerator(k, size());
		}
	}

	protected abstract BigIntegerSubsetEnumerator getBigSubsetEnumerator(int k);

	protected abstract SubsetEnumerator getSubsetEnumerator(int k, int n);

	protected abstract boolean needBigInteger();

	abstract class SubsetEnumerator extends EnumerableValue.SubsetEnumerator {
		public SubsetEnumerator(final int k, final int n) {
			super(k, n);
		}

		@Override
		public Value nextElement() {
			if (!hasNext()) {
				return null;
			}
			return elementAt(nextIndex());
		}

		protected abstract Value elementAt(int nextIndex);
	}

	abstract class BigIntegerSubsetEnumerator implements ValueEnumeration {

		protected final BigInteger x;
		protected final BigInteger a;

		protected final int k;
		
		protected BigInteger sz;
		protected int i;

		public BigIntegerSubsetEnumerator(final int k) {
			this.k = k;
			this.i = 0;

			this.a = BigInteger.valueOf(Math.abs(RandomEnumerableValues.get().nextLong()));

			// http://primes.utm.edu/lists/2small/0bit.html
			// (2^63 - 25)
			this.x = BigInteger.valueOf(Long.MAX_VALUE - 24L);
		}

		private BigInteger nextIndex() {
			// ((x * i) + a) % sz
			final BigInteger bi = BigInteger.valueOf(this.i++);
			final BigInteger multiply = this.x.multiply(bi);
			return multiply.add(this.a).mod(this.sz);
		}

		@Override
		public void reset() {
			this.i = 0;
		}

		private boolean hasNext() {
			return this.i < this.k;
		}

		@Override
		public Value nextElement() {
			if (!hasNext()) {
				return null;
			}
			return elementAt(nextIndex());
		}

		protected abstract Value elementAt(BigInteger nextIndex);
	}
}
