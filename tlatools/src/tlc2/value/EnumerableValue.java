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
import tlc2.tool.TLCState;
import tlc2.util.IdThread;

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
  
	@Override
	public EnumerableValue getRandomSubset(final int kOutOfN) {
		// By default, convert all EVs into SetEnumValue and delegate to its
		// getRandomSubset.
    	return SetEnumValue.convert(this).getRandomSubset(kOutOfN);
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
		final List<Value> values = elements().all();
		return new SubsetEnumerator(k) {
			@Override
			public Value nextElement() {
				if (!hasNext()) {
					return null;
				}
				return values.get(nextIndex());
			}
		};
  	}

	/* Randomization for sets */
	
	static {
		// see java.util.Random.seedUniquifier()
		randomSeed = (8682522807148012L * 181783497276652981L) ^ System.nanoTime();
	}
		
	private static long randomSeed; 
	
	public static long getRandomSeed() {
		return randomSeed;
	}
	
	/**
	 * Initialize Random with the given seed value.
	 **/
	public static void setRandom(final long seed) {
		randomSeed = seed;
		resetRandom();
	}
	
	/**
	 * Re-Initialize Random with the recorded seed value.
	 **/
	public static void resetRandom() {
		RANDOMS.remove();
	}

	public static Random getRandom() {
		return RANDOMS.get();
	}
	
	// In order to recreate the error trace - which essentially corresponds to
	// rerunning state exploration following a given path - we have to recreate the
	// same random values too. Otherwise, TLC will fail to recreate the trace
	// because the recreated TLCState does not match the fingerprint in the error
	// trace/path. Therefore, we maintain one RNG per IdThread (IWorker) which - for
	// the initial states - is seeded with enumFractionSeed and - in the scope of
	// next-state - gets seeded with the fingerprint of the predecessor state.
	private static final ThreadLocal<Random> RANDOMS = new ThreadLocal<Random>() {
		@Override
		protected Random initialValue() {
			return new Random(randomSeed);
		}
		@Override
		public Random get() {
			final Random random = super.get();
			
			final TLCState tlcState = IdThread.getCurrentState();
			if (tlcState != null) {
				random.setSeed(tlcState.fingerPrint());
			}
			
			return random;
		}
	};

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
				this.a = getRandom().nextInt(n);
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

		public abstract Value nextElement();
	}
}
