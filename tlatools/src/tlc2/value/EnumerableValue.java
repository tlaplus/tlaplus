/*******************************************************************************
 * Copyright (c) 2017 Microsoft Research. All rights reserved.
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

import java.util.List;

import tlc2.tool.FingerprintException;

public abstract class EnumerableValue extends Value implements Enumerable {

  public IValue isSubsetEq(IValue other) {
    try {
      final ValueEnumeration Enum = this.elements();
      IValue elem;
      while ((elem = Enum.nextElement()) != null) {
        if (!other.member(elem)) {
          return ValFalse;
        }
      }
      return ValTrue;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }
  
	@Override
	public EnumerableValue getRandomSubset(final int kOutOfN) {
		// By default, convert all EVs into SetEnumValue and delegate to its
		// getRandomSubset.
    	return ((SetEnumValue) this.toSetEnum()).getRandomSubset(kOutOfN);
	}

	@Override
	public ValueEnumeration elements(final Ordering ordering) {
		if (ordering == Ordering.NORMALIZED) {
			// By default, none of the EnumerableValues supports a ValueEnumeration that
			// provides normalized ordering. Thus, to traverse the elements in normalized
			// ordering, any EV type gets converted into a SetEnumValue - this effectively
			// enumerates the EV and normalizes the new SEV. Traversing the normalized
			// SEV with a ValueEnumeration returned by Enumerable#elements is guaranteed 
			// to be in normalized order (@see Ordering.NORMALIZED for what this means).
			// In case a subclass provides a more efficient ValueEnumeration that guarantees
			// normalized order, the subclass may override this default method. This is
			// so far done by SubsetValue.
			final IValue enumerated = this.toSetEnum();
			if (enumerated != null) {
				return ((EnumerableValue) enumerated.normalize()).elements();
			}
		}
		return elements();
	}
	
	public ValueEnumeration elements(final int k) {
		// The generic implementation collects all n elements of the actual Enumerable
		// into the temporary variable values. The SubSetEnumerator then randomly
		// returns up to k elements.
		// The underlying assuming here is that the size of EnumerableValue (n) is
		// very small and this method is not called as part of the next-state relation.
		// If it gets called on larger sets or as part of the next-state relation,
		// subclasses can provide a more efficient implementation (e.g. see
		// IntervalValue and SetEnumValue which return a more efficient subclass
		// of SubsetEnumerator).
		final List<IValue> values = elements().all();
		return new SubsetEnumerator(k) {
			@Override
			public IValue nextElement() {
				if (!hasNext()) {
					return null;
				}
				return values.get(nextIndex());
			}
		};
  	}

	abstract class SubsetEnumerator implements ValueEnumeration {

		protected final long x;
		protected final int a;
		protected final int n;
		protected final int k;
		protected int i;

		public SubsetEnumerator(final int k) {
			this(k, size());	
		}
		
		public SubsetEnumerator(final int k, final int n) {
			this.n = n;
			
			// https://en.wikipedia.org/wiki/Linear_congruential_generator
			//
			// x has to be co-prime to n. Since n might or might not be a prime number
			// - it depends on the actual size of the set - we simply set x to
			// be a prime number. The prime x has to be larger than n tough, since n is
			// bound by Integer.MAX_VALUE, we simply choose the Mersenne prime
			// Integer.MAX_VALUE
			// for x and accept that we fail if n = Integer.MAX_VALUE. To minimize
			// intermediate results and the rounds of mod in nextIndex, we choose 191 if n
			// happens to be smaller (very likely).
			assert n < Integer.MAX_VALUE;
			this.x = n < 191 ? 191L : 1L * Integer.MAX_VALUE;

			// k out of n elements in the range 0 <= k <= n.
			if (n > 0) {
				this.k = k;
				this.a = RandomEnumerableValues.get().nextInt(n);
			} else {
				this.k = 0;
				this.a = 0; // RANDOM.nextInt(0) causes IllegalArgumentException.
			}
		}

		public void reset() {
			i = 0;
		}

		public boolean hasNext() {
			return i < k;
		}

		/**
		 * @return A random (uniformly distributed) index in the range [0,n) where n is
		 *         {@link Enumerable#size()}.
		 */
		public int nextIndex() {
			if (n <= 0) {
				i++;
				return 0;
			}
			// long x avoids intermediate overflow, final cast to int safe though because of
			// mod n.
			final int index = (int) (((x * i++) + a) % n);
			assert 0 <= index && index < n;
			return index;
		}

		public abstract IValue nextElement();
	}
}
