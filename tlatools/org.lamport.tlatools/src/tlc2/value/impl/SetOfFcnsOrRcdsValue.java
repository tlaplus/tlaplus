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

/**
 * Base class for the set of functions [S -> T] (SetOfFcnsValue), the set of records
 * [h_1: S_1, ..., h_n: S_n] (SetOfRcdsValue), and the Cartesian product
 * S_1 \X ... \X S_n (SetOfTuplesValue). All three are sets of functions whose
 * cardinality is a product of the cardinalities of their constituent sets, which is why
 * they share the (big-integer) subset enumeration below.
 */
public abstract class SetOfFcnsOrRcdsValue extends EnumerableValue {

	// A record is a function whose domain is the set of its field names, and a tuple
	// one whose domain is an interval 1..n, which is why SetOfRcdsValue and
	// SetOfTuplesValue share this class with SetOfFcnsValue:
	//
	// THEOREM \A S, T : [h: S, g: T] \subseteq [{"h", "g"} -> S \cup T]
	// THEOREM \A S : [h: S, g: S] = [{"h", "g"} -> S]
	// THEOREM \A S, T : S \X T \subseteq [1..2 -> S \cup T]
	// THEOREM \A S : S \X S = [1..2 -> S]
	//
	// The theorems are the case n = 2 of the claims about [h_1: S_1, ..., h_n: S_n]
	// and S_1 \X ... \X S_n. A theorem has to fix n because TLA+ requires the fields
	// of a record set and the components of a product to be written out; an arbitrary
	// n has to be stated as a set of functions from the field names or from 1..n to
	// the union of the constituent sets, i.e. as a construct other than the ones that
	// SetOfRcdsValue and SetOfTuplesValue implement. There is no record with n = 0
	// because [] is not TLA+; the record without fields is the empty function <<>>,
	// which is also the sole element of [{} -> T] and what a product never contains.
	//
	// What the subclasses share is neither equals nor member nor size, but that an
	// index in 0..(Cardinality(this) - 1) determines an element without enumerating
	// its predecessors. All three are a product of the constituent sets that Product
	// reports below, so an index read in the mixed radix of their cardinalities
	// yields one value per constituent, and those values make up an element.

	// The constituent sets of this set, one per digit of the index that the
	// enumerators below decode, from the most to the least significant, and the
	// element that one value per constituent set makes up. SetOfFcnsValue repeats its
	// co-domain once per element of the domain, i.e. its radix is fixed, whereas
	// SetOfRcdsValue reports one set per field and SetOfTuplesValue one per component.
	abstract class Product {

		abstract SetEnumValue[] constituents();

		abstract Value elementOf(Value[] values);
	}

	protected abstract Product product();

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
			return new BigIntegerSubsetEnumerator(k);
		} else {
			return new SubsetEnumerator(k, size());
		}
	}

	protected abstract boolean needBigInteger();

	final class SubsetEnumerator extends EnumerableValue.SubsetEnumerator {

		private final Product product;
		private final SetEnumValue[] constituents;
		private final int[] rescaleBy;

		SubsetEnumerator(final int k, final int n) {
			super(k, n);

			this.product = product();
			this.constituents = product.constituents();
			this.rescaleBy = new int[constituents.length];

			int numElems = 1; // 1 to avoid div by zero in elementAt
			for (int i = constituents.length - 1; i >= 0; i--) {
				rescaleBy[i] = numElems;
				numElems *= constituents[i].elems.size();
			}
		}

		@Override
		public Value nextElement() {
			if (!hasNext()) {
				return null;
			}
			return elementAt(nextIndex());
		}

		Value elementAt(final int idx) {
			assert 0 <= idx && idx < size();

			final Value[] values = new Value[constituents.length];
			for (int i = 0; i < values.length; i++) {
				final ValueVec elems = constituents[i].elems;
				values[i] = elems.elementAt((idx / rescaleBy[i]) % elems.size());
			}
			return product.elementOf(values);
		}
	}

	final class BigIntegerSubsetEnumerator implements ValueEnumeration {

		private final BigInteger x;
		private final BigInteger a;

		private final int k;

		private final Product product;
		private final SetEnumValue[] constituents;
		private final BigInteger[] rescaleBy;

		private final BigInteger sz;
		private int i;

		public BigIntegerSubsetEnumerator(final int k) {
			this.k = k;
			this.i = 0;

			this.a = BigInteger.valueOf(Math.abs(RandomEnumerableValues.get().nextLong()));

			// http://primes.utm.edu/lists/2small/0bit.html
			// (2^63 - 25)
			this.x = BigInteger.valueOf(Long.MAX_VALUE - 24L);

			this.product = product();
			this.constituents = product.constituents();
			this.rescaleBy = new BigInteger[constituents.length];

			BigInteger numElems = BigInteger.ONE; // 1 to avoid div by zero in elementAt
			for (int j = constituents.length - 1; j >= 0; j--) {
				rescaleBy[j] = numElems;
				numElems = numElems.multiply(BigInteger.valueOf(constituents[j].elems.size()));
			}

			// The size of the (enumerated) SetOfFcnsOrRcdsValue needs BigInteger.
			this.sz = numElems;
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

		private Value elementAt(final BigInteger idx) {
			final Value[] values = new Value[constituents.length];
			for (int j = 0; j < values.length; j++) {
				final ValueVec elems = constituents[j].elems;
				final BigInteger mod = BigInteger.valueOf(elems.size());
				values[j] = elems.elementAt(idx.divide(rescaleBy[j]).mod(mod).intValueExact());
			}
			return product.elementOf(values);
		}
	}
}
