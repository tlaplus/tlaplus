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

package tlc2.value.impl;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.concurrent.ConcurrentHashMap;

import org.apache.commons.math3.primes.Primes;

import tlc2.tool.FingerprintException;
import tlc2.util.RandomGenerator;
import tlc2.value.RandomEnumerableValues;

public abstract class EnumerableValue extends Value implements Enumerable {

  @Override
  public Value isSubsetEq(Value other) {
    try {
      final ValueEnumeration Enum = this.elements();
      Value elem;
      while ((elem = Enum.nextElement()) != null) {
        if (!other.member(elem)) {
          return BoolValue.ValFalse;
        }
      }
      return BoolValue.ValTrue;
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
				return ((Enumerable) enumerated.normalize()).elements();
			}
		} else if (ordering == Ordering.RANDOMIZED) {
			return elements(size());
		}
		return elements();
	}
	
	@Override
	public ValueEnumeration elements(final int k) {
		// The generic implementation collects all n elements of the actual Enumerable
		// into the temporary variable values. The SubSetEnumerator then randomly
		// returns up to k elements.
		// The underlying assuming here is that the size of Enumerable (n) is
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

	abstract class SubsetEnumerator implements ValueEnumeration {

		// n is the upper bound for the range for which nextIndex returns values.
		protected final int n;

		// k is the number of times nextIndex can be called.
		protected final int k;
		// i counts the number of calls.
		protected int i;
		
		// The seed, X, index, ...
		private int index; // X_i or seed
		// Multiplier (long because intermediate values in nextIndex can exceed Int.MAX_VALUE)
		protected long a;
		// Modulo
		private int m;
		// Increment
		private int c;

		public SubsetEnumerator(final int k) {
			this(k, size());	
		}
		
		public SubsetEnumerator(final int k, final int n) {
			if (n <= 0) {
				// For n < 1, hasNext is always going to return false.
				this.n = 0;
				this.k = 0;
				return;
			}
			
			this.n = n;
			this.k = k;

			// Calculating optimal parameters for the given n is expensive! We assume that
			// we will only have to calculate parameters for a small number of ns per
			// model-checker run.
			int[] vals = MULTIPLIERS.computeIfAbsent(n, j -> computeOptimalMandA(j));
			this.m = vals[0];
			this.a = vals[1];
			
			final Random random = RandomEnumerableValues.get();
			this.index = random.nextInt(n);
			// Choose a prime for c that is guaranteed to be co-prime with m. We randomly
			// choose a prime number on every invocation to better approximate a uniform
			// distribution for repeated evaluation of Randomization!RandomSubset(k, S) with
			// k and S fixed to some values.  Since TLC cheats and evaluates RandomSubset
			// simply by generating k indices in 0..|S|, repeatedly evaluating RandomSubset
			// will reveal a bias because -even though the individual indices are uniform-
			// the *sequences* of indices generated are not uniformly distributed. A more
			// costly implementation that's based on generating the indices of all ksubsets
			// of S and SubsetValue#getUnrank(k) would be robust against a static increment
			// c.  For S = 1..20 and k = 3, this implementation is roughly 2.5x better in
			// approximating a uniform distribution yet also 2.5x slower.
			this.c = RandomGenerator.nextPrime(random);
		}

		@Override
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
			do {
				index = (int) ((this.a * index + this.c) % this.m);
			} while (index >= this.n);
			i++;
			assert 0 <= index && index < this.n;
			return index;
		}

		@Override
		public abstract Value nextElement();
	}
	
	// Consider bootstrapping the parameters for the upper range of Integers (where
	// prime factorization becomes more expensive)?
	private static Map<Integer, int[]> MULTIPLIERS = new ConcurrentHashMap<>();

	// https://en.wikipedia.org/wiki/Linear_congruential_generator#c_%E2%89%A0_0
	// When c # 0, correctly chosen parameters allow a period equal to m, for all seed values. This will occur iff:
	// m and c are relatively prime,
	// a-1 is divisible by all prime factors of m
	// a-1 is divisible by 4 if m is divisible by 4.
	static int[] computeOptimalMandA(int n) {
		if (n < 9) {
			// while loop will increment n to 9 for all values lower than 9 anyway.
			n = 9;
		}

		// Prime factorization is expensive!!! As a minor optimization, we could in-line
		// primeFactor and use counters and track the product while looping instead of
		// storing all primes in a list, comparing its size to the set, and calculating
		// the product of the set.  However, I don't want to spend the time to extract
		// Apache Commons Math's primeFactors implementation.
		List<Integer> primeFactors = Primes.primeFactors(n);
		while (n % 4 == 0 || new HashSet<>(primeFactors).size() == primeFactors.size()) {
			n = n + 1;
			primeFactors = Primes.primeFactors(n);
		}

		int a = 1;
		for (Integer prime : new HashSet<>(primeFactors)) {
			a *= prime;
		}
		a += 1;
		
		// Unfortunately, Java doesn't have tuples/pairs.
		return new int[] {n, a};
	}
}

/*
---- CONFIG ksubsets_random_subset ----
CONSTANTS 
    Elements={1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20}
    Limit=1000
SPECIFICATION   Spec
====

------------------------------ MODULE ksubsets_random_subset ------------------------------
EXTENDS Naturals, Randomization, FiniteSets, TLC

CONSTANT Elements,
         Limit

VARIABLES counts,
          total

vars == <<counts, total >>

AddSubset ==
    /\ total < Limit 
    /\ \E ss \in { RandomSubset(3, Elements) } :
        /\ IF ss \in DOMAIN counts
            THEN counts' = [counts EXCEPT ![ss] = @ + 1]
            ELSE counts' = counts @@ (ss :> 1)
        /\ total' = total + 1

PrintDist ==
    /\ total = Limit
    /\ total' = Limit + 1
    /\ UNCHANGED <<counts>>
    /\ \A ss \in DOMAIN counts : PrintT(<<total, ss, counts[ss]>>)
    /\ PrintT(<<"RESULT", Cardinality(DOMAIN counts)>>)

Init == 
    /\ counts = [ss \in {} |-> 0]
    /\ total = 0

Next ==
    \/ AddSubset
    \/ PrintDist

Spec == Init /\ [][Next]_vars  

=============================================================================
\* Modification History
\* Last modified Tue Oct 27 17:24:00 CET 2020 by jvanlightly
\* Created Tue Oct 27 09:55:35 CET 2020 by jvanlightly
*/