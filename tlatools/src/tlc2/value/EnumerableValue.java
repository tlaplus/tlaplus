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

import tlc2.TLCGlobals;
import tlc2.tool.FingerprintException;
import tlc2.tool.ModelChecker;
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
			final Value enumerated = this.toSetEnum();
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
	
	private static final ThreadLocal<Random> RANDOMS = new ThreadLocal<Random>() {
		@Override
		protected Random initialValue() {
			if (TLCGlobals.mainChecker != null && ModelChecker.class.equals(TLCGlobals.mainChecker.getClass())) {
				// In order to recreate the error trace in BFS mode - which essentially
				// corresponds to rerunning state exploration following a given path - we have
				// to recreate the same random values too. Otherwise, TLC will fail to recreate
				// the trace because the recreated TLCState does not match the fingerprint in
				// the error trace/path. Therefore, we maintain one RNG per IdThread (IWorker)
				// which - for the initial states - is seeded with enumFractionSeed and - in the
				// scope of next-state - gets seeded with the fingerprint of the predecessor
				// state.
				return new TLCStateRandom(randomSeed);
			} else {
				// DFS or Simulation need no special handling because:
				// - DFS does not re-create the error trace (just prints the current trace).
				// - Simulation mode is intended to allow users to gather statistics on
				// behaviors generated with specified probabilities of different transitions.
				// (For example, to find the expected time for a message to be delivered with
				// retransmission as a function of the probability of message loss). For this,
				// it's important that the random choice have no correlation with the state in
				// which the choice is made.
				return new DefaultRandom(randomSeed);
			}
		}

		@Override
		public Random get() {
			// Hook to re-initialize random (no-op for DFS and simulation).
			return ((EnumerableValueRandom) super.get()).initialize();
		}
	};
		
	private static interface EnumerableValueRandom {
		public Random initialize();
	}

	@SuppressWarnings("serial")
	private static final class DefaultRandom extends Random implements EnumerableValueRandom {
		public DefaultRandom(long randomSeed) {
			super(randomSeed);
		}

		@Override
		public final Random initialize() {
			// Noop
			return this;
		}
	}

	@SuppressWarnings("serial")
	private static final class TLCStateRandom extends Random implements EnumerableValueRandom {

		private TLCState state;

		public TLCStateRandom(long randomSeed) {
			super(randomSeed);
		}

		private void initializedFor(final TLCState state) {
			// XOR the state's fingerprint with the initial randomSeed value. This is done
			// so that two identical states (same fingerprint) of two different
			// specifications do not produce the same random value.
			final long seed = state.fingerPrint() ^ randomSeed;
			this.setSeed(seed);
			this.state = state;
		}

		private boolean isInitializedFor(final TLCState another) {
			return state == another;
		}

		@Override
		public Random initialize() {
			final TLCState state = IdThread.getCurrentState();
			// state is null during the generation of initial states and non-null in the
			// scope of the next-state relation (however, state can be an initial state).
			// Thus, an RNG is seeded with randomSeed during the generation of initial
			// states and seeded with randomSeed ^ predecessor's fingerprint during the
			// generation of next states.
			// Do not re-initialize random for the same TLCState twice to produce two
			// distinct values with high probability with a next-state such as:
			// Next == x' = RandomElement(0..2) /\ y' = RandomElement(0..2)
			// If random was to be re-initialized/re-seeded, RandomElement(0..2) for x' and y'
			// would be identical values (also see tlc2.tool.RandomElementXandYTest).
			if (state != null && !isInitializedFor(state)) {
				initializedFor(state);
			}
			return this;
		}
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
