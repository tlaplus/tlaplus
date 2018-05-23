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
import java.util.Random;

import tlc2.tool.FingerprintException;

public abstract class EnumerableValue extends Value implements Enumerable, ValueConstants {

  public Value isSubsetEq(Value other) {
    try {
      final ValueEnumeration Enum = this.elements();
      Value elem;
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
  
	public ValueEnumeration elements(final double fraction) {
		// The generic implementation collects all n elements of the actual Enumerable
		// into the temporary variable values. The SubSetEnumerator then randomly
		// returns up to (fraction * n) of elements.
		// The underlying assuming here is that the size of EnumerableValue (n) is
		// very small and this method is not called as part of the next-state relation.
		// If it gets called on larger sets or as part of the next-state relation,
		// subclasses can provide a more efficient implementation (e.g. see
		// IntervalValue and SetEnumValue which return a more efficient subclass
		// of SubsetEnumerator).
		final List<Value> values = elements().all();
		return new SubsetEnumerator(fraction) {
			@Override
			public Value nextElement() {
				if (!hasNext()) {
					return null;
				}
				return values.get(nextIndex());
			}
		};
	}

	static {
		enumFractionSeed = System.currentTimeMillis();		
	}
		
	public static long enumFractionSeed; 
	
	/**
	 * Re-Initialize Random with the recorded seed value.
	 **/
	public static void resetRandom() {
		RANDOM.setSeed(enumFractionSeed);
	}
	
	protected static final Random RANDOM = new Random(enumFractionSeed);

	abstract class SubsetEnumerator implements ValueEnumeration {

		protected final long x;
		protected final int a;
		protected final int n;
		protected final int k;
		protected int i;

		public SubsetEnumerator(final double fraction) {
			this(fraction, size());
		}
		
		public SubsetEnumerator(final double fraction, final int n) {
			this.n = n;
			
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

			this.a = RANDOM.nextInt(n);
			// k out of n elements in the range 0 <= k <= n.
			this.k = (int) Math.min(Math.ceil(fraction * n), n);
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
			// long x avoids intermediate overflow, final cast to int safe though because of
			// mod n.
			final int index = (int) (((x * i++) + a) % n);
			assert 0 <= index && index < n;
			return index;
		}

		public abstract Value nextElement();
	}
}
