// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 13:46:07 PST by lamport
//      modified on Fri Aug 10 15:10:16 PDT 2001 by yuanyu

package tlc2.value;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.BitSet;
import java.util.Collection;
import java.util.HashSet;
import java.util.Random;
import java.util.TreeMap;

import tlc2.output.EC;
import tlc2.tool.FingerprintException;
import tlc2.util.Combinatorics;
import util.Assert;

public class SubsetValue extends EnumerableValue implements Enumerable {
  public Value set;           // SUBSET set
  protected SetEnumValue pset;

  /* Constructor */
  public SubsetValue(Value set) {
    this.set = set;
    this.pset = null;
  }

  public final byte getKind() { return SUBSETVALUE; }

  public final int compareTo(Object obj) {
    try {
      if (obj instanceof SubsetValue) {
        return this.set.compareTo(((SubsetValue)obj).set);
      }
      this.convertAndCache();
      return this.pset.compareTo(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      if (obj instanceof SubsetValue) {
        return this.set.equals(((SubsetValue)obj).set);
      }
      this.convertAndCache();
      return this.pset.equals(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean member(Value val) {
    try {
      if (val instanceof Enumerable) {
        ValueEnumeration Enum = ((Enumerable)val).elements();
        Value elem;
        while ((elem = Enum.nextElement()) != null) {
          if (!this.set.member(elem)) {
        	  return false;
          }
        }
      }
      else {
        Assert.fail("Attempted to check if the non-enumerable value\n" +
        ppr(val.toString()) + "\nis element of\n" + ppr(this.toString()));
      }
      return true;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public Value isSubsetEq(Value other) {
    try {
      // Reduce (SUBSET A \subseteq SUBSET B) to (A \subseteq B) to avoid
      // exponential blowup inherent in generating the power set.
      if (other instanceof SubsetValue && this.set instanceof EnumerableValue) {
        final SubsetValue sv = (SubsetValue) other;
        return ((EnumerableValue) this.set).isSubsetEq(sv.set);
      }
      return super.isSubsetEq(other);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isFinite() {
    try {
      return this.set.isFinite();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value takeExcept(ValueExcept ex) {
    try {
      if (ex.idx < ex.path.length) {
        Assert.fail("Attempted to apply EXCEPT to the set " + ppr(this.toString()) + ".");
      }
      return ex.value;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value takeExcept(ValueExcept[] exs) {
    try {
      if (exs.length != 0) {
        Assert.fail("Attempted to apply EXCEPT to the set " + ppr(this.toString()) + ".");
      }
      return this;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final int size() {
    try {
      int sz = this.set.size();
      if (sz >= 31) {
        Assert.fail(EC.TLC_MODULE_OVERFLOW, "the number of elements in:\n" +
        ppr(this.toString()));
      }
      return (1 << sz);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isNormalized() {
    try {
      return (this.pset != null &&
        this.pset != DummyEnum &&
        this.pset.isNormalized());
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value normalize() {
    try {
      if (this.pset == null || this.pset == DummyEnum) {
        this.set.normalize();
      }
      else {
        this.pset.normalize();
      }
      return this;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isDefined() {
    try {
      return this.set.isDefined();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) {
    try {
      return this.equals(val);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* The fingerprint  */
  public final long fingerPrint(long fp) {
    try {
      this.convertAndCache();
      return this.pset.fingerPrint(fp);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value permute(MVPerm perm) {
    try {
      this.convertAndCache();
      return this.pset.permute(perm);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  private final void convertAndCache() {
    if (this.pset == null) {
      this.pset = this.toSetEnum();
    }
    else if (this.pset == DummyEnum) {
      SetEnumValue val = null;
      synchronized(this) {
        if (this.pset == DummyEnum) {
          val = this.toSetEnum();
          val.deepNormalize();
        }
      }
      synchronized(this) {
        if (this.pset == DummyEnum) { this.pset = val; }
      }
    }
  }

  @Override
  public SetEnumValue toSetEnum() {
      if (this.pset != null && this.pset != DummyEnum) {
        return this.pset;
      }
      ValueVec vals = new ValueVec(this.size());
      ValueEnumeration Enum = this.elements();
      Value elem;
      while ((elem = Enum.nextElement()) != null) {
        vals.addElement(elem);
      }
      // For as long as pset.elements() (SubsetValue#elements)
      // internally calls SubsetValue#elementsNormalized, the
      // result SetEnumValue here is indeed normalized.
      return new SetEnumValue(vals, true);
  }

  /* The string representation  */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    try {
      boolean unlazy = expand;
      try {
        if (unlazy) {
          unlazy = this.set.size() < 7;
        }
      }
      catch (Throwable e) { unlazy = false; }

      if (unlazy) {
        Value val = this.toSetEnum();
        return val.toString(sb, offset);
      }
      else {
        sb = sb.append("SUBSET ");
        sb = this.set.toString(sb, offset);
        return sb;
      }
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }  
  
  	public Unrank getUnrank(final int kSubset) {
		// Convert outer set only once.
		final SetEnumValue convert = set.toSetEnum();
		convert.normalize();
		final ValueVec elems = convert.elems;

		return new Unrank(kSubset, Combinatorics.bigSumChoose(elems.size(), kSubset).longValueExact(),
				Combinatorics.pascalTableUpTo(elems.size(), kSubset), elems, kSubset);
  	}
 
	public EnumerableValue getRandomSetOfSubsets(final int numOfSubsetsRequested, final int maxLengthOfSubsets) {
		// Convert outer set only once.
		final SetEnumValue convert = set.toSetEnum();
		convert.normalize();
		final ValueVec elems = convert.elems;
		final int size = elems.size();

		// Calculate the sums of the rows of the Pascal Triangle up to
		// maxLengthOfSubsets.
		final long[] kss = new long[maxLengthOfSubsets + 1];
		kss[0] = 1L;
		// Sum the elems.size()'s row of the Pascal Triangle up to maxLengthOfSubsets.
		// This corresponds to Combinatorics.bigSumChoose except that we also keep the
		// intermediate results.
		BigInteger sum = BigInteger.ONE; // 1 for k=0
		for (int i = 1; i <= maxLengthOfSubsets; i++) {
			kss[i] = Combinatorics.bigChoose(size, i).longValueExact();
			sum = sum.add(BigInteger.valueOf(kss[i]));
		}
		assert sum.equals(Combinatorics.bigSumChoose(size, maxLengthOfSubsets));

		// Extend existing Pascal Triangle by a table for the k's 2..maxLengthOfSubset
		// for all n up to |S| (if needed, otherwise long[0]).
		final long[] ppt = Combinatorics.pascalTableUpTo(size, maxLengthOfSubsets);

		final ValueVec vec = new ValueVec(numOfSubsetsRequested);
		for (int rank = 0; rank < kss.length; rank++) {
			final BigDecimal divide = BigDecimal.valueOf(kss[rank]).divide(new BigDecimal(sum), 32,
					BigDecimal.ROUND_HALF_DOWN);
			// Small bias towards smaller/shorter k-Subsets because 0 gets rounded up to 1.
			final long n = divide.multiply(BigDecimal.valueOf(numOfSubsetsRequested)).max(BigDecimal.ONE).toBigInteger()
					.longValueExact();

			// The last one (kSubsetSizes.length - 1) is generates the outstanding
			// number of subsets (will be close to its calculated n anyway).
			final RandomUnrank unrank = new RandomUnrank(rank,
					rank == kss.length - 1 ? numOfSubsetsRequested - vec.size() : n, ppt, elems, maxLengthOfSubsets,
					EnumerableValue.getRandom());

			Value subset;
			while ((subset = unrank.randomSubset()) != null && vec.size() < numOfSubsetsRequested) {
				vec.addElement(subset);
			}
		}
		assert vec.size() == numOfSubsetsRequested;
		return new SetEnumValue(vec, false);
	}

	public class Unrank {

		private final TreeMap<Long, Integer> sums = new TreeMap<>();
		private final long[] partialPascalTable;
		private final int maxK;

		private final ValueVec elems;

		private final int k; // rank of k-Subset

		public Unrank(final int k, final long n, final long[] ppt, final ValueVec elems, final int maxK) {
			this.k = k;
			this.elems = elems;
			this.partialPascalTable = ppt;
			this.maxK = maxK - 1;

			// Cache the sum of all binomials lt n for 0..elems.size choose k.
			int choice = Math.max(k - 1, 0);
			sums.put(-1L, choice); // As base for idx = 0 (see lowerEntry below);
			long bin = 0L;
			while ((bin = memoizedBinomial(choice, k)) < n) {
				sums.put(bin, ++choice);
			}
		}

		public Value subsetAt(long idx) {
			// More subsets in this kSubset available.
			final ValueVec vec = new ValueVec(k);

			int y = k, choice = sums.lowerEntry(idx).getValue();
			for (; choice >= 0 && k > 0; choice--) {
				final long c = memoizedBinomial(choice, y);
				if (c <= idx) {
					idx -= c;
					y--;
					vec.addElement(this.elems.elementAt(choice));
				}
			}
			return new SetEnumValue(vec, false);
		}

		protected long memoizedBinomial(final int n, final int k) {
			if (k == 0 || k == n) {
				return (long) 1;
			} else if (k == 1 || k == n - 1) {
				return (long) n;
			} else if (n == 0 || k > n) {
				// Cannot choose from zero elements or more elements than present.
				return 0;
			}
			final int pti = Combinatorics.choosePairToInt(n, k);
			if (pti < Combinatorics.CHOOSETABLE.length) {
				return Combinatorics.choose(n, k);
			}
			return partialPascalTable[(n - Combinatorics.MAXCHOOSENUM - 1) * maxK + k - 2];
		}
	}

	private class RandomUnrank extends Unrank {

		// Primes taken from: https://primes.utm.edu/lists/2small/0bit.html
		// TODO: 9223372036854775783L; // 2^63 - 25
//		private static final long x = 549755813881L; // 2^39 - 7 
		private static final long x = 34359738337L; // 2^35 - 31

		private final long n;
		private final long a;
		private long i;

		public RandomUnrank(final int k, final long n, final long[] ppt, final ValueVec elems, final int maxK,
				final Random random) {
			super(k, n, ppt, elems, maxK);
			this.n = n;
			this.a = Math.abs(random.nextLong()) % n;
		}

		public Value randomSubset() {
			if (i < n) {
				return subsetAt(((x * i++) + a) % n);
			}
			return null;
		}
	}

	public EnumerableValue getRandomSetOfSubsets(final int numOfPicks, final double probability) {
		final CoinTossingSubsetEnumerator enumerator = new CoinTossingSubsetEnumerator(numOfPicks, probability);
		
		// Using a set here instead of ValueVec preserves the set invariant (no
		// duplicates). The alternative - a ValueVec which gets sorted to remove
		// duplicates after the while loops is slower.
		final int estimated = (int) (numOfPicks * probability);
		final Collection<Value> sets = new HashSet<>(estimated);
		Value val;
		while ((val = enumerator.nextElement()) != null) {
			sets.add(val);
		}
		
		return new SetEnumValue(new ValueVec(sets), false);
	}
	
	private final ValueEnumeration emptyEnumeration = new ValueEnumeration() {
		private boolean done = false;

		@Override
		public void reset() {
			done = false;
		}
		
		@Override
		public Value nextElement() {
			if (done) { return null; }
			done = true;
			return new SetEnumValue();
		}
	};

	/**
	 * @see file SubsetValue.tla.
	 * <p>
	 * In addition, this generates all subsets of this SubsetValue instance which extends
	 * the order definition given in SubsetValue.tla such that a subset s is considered 
	 * lower than t (s < t) if Cardinality(s) < Cardinality(t) \/ Definition in SubsetValue.tla.
	 * <p>
	 * The most noteworthy difference between bElements and 
	 */
	final ValueEnumeration elementsNormalized() {
		final int n = set.size();
		if (n == 0) {
			emptyEnumeration.reset();
			return emptyEnumeration;
		}
		// Only normalized inputs will yield a normalized output. Note that SEV#convert
		// (unfortunately) enumerates the input. Thus "SUBSET SUBSET 1..10" will result
		// in the nested/right SUBSET to be fully enumerated (1..10 obviously too).
		final ValueVec elems = ((SetEnumValue) set.toSetEnum().normalize()).elems;
		return new ValueEnumeration() {

			private int k = 0;
			private final int[] indices = new int[n];

			@Override
			public void reset() {
				reset(0);
			}

			private void reset(final int k) {
				this.k = k;
				if (k > n) {
					return;
				}
				for (int i = 0; i < k; i++) {
					indices[i] = i;
				}
			}

			@Override
			public Value nextElement() {
				if (k > n) {
					return null;
				} else if (k == 0) {
					reset(k + 1);
					return new SetEnumValue();
				}

				final ValueVec vals = new ValueVec(k);
				int i = k - 1;
				for (int j = i; j >= 0; j--) {
					vals.addElementAt(elems.elementAt(indices[j]), j);
					if (indices[j] + k - j == n) {
						i = j - 1;
					}
				}
				final SetEnumValue result = new SetEnumValue(vals, true);

				if (indices[0] == n - k) {
					// Increment k to generate the set of k-subset for this k.
					reset(k + 1);
					return result;
				}

				// Increment the right element r by one and remember its old value.
				indices[i]++;

				// Adjust all the elements right to the right element r. For all indices j > i,
				// the element at j is set to p[i] + j.
				for (i++; i < k; i++) {
					indices[i] = indices[i - 1] + 1;
				}
				return result;
			}
		};
	}
	
	/**
	 * @see SubsetValue#kElements(int)
	 */
	public final long numberOfKElements(final int k) {
		final int size = this.set.size();
		if (k < 0 || size < k || size > 62) {
			throw new IllegalArgumentException(String.format("k=%s and n=%s", k, size));
		}
		if (k == 0 || k == size) {
			return 1;
		}
		return Combinatorics.choose(size, k);
	}
	
	/**
	 * [S]^k (sometimes denoted S^[k]) == { t \in SUBSET S : Cardinality(t) = k }
	 * @param k
	 * @return
	 */
	public final ValueEnumeration kElements(final int k) {
		if (k < 0 || this.set.size() < k) {
			throw new IllegalArgumentException();
		}
		if (k == 0) {
			emptyEnumeration.reset();
			return emptyEnumeration;
		}

		return new KElementEnumerator(k);
	}
	
	public final class KElementEnumerator implements ValueEnumeration {
		private final ValueVec elems;
		private final int numKSubsetElems;
		private final int k;
		
		private int index;
		private int cnt;

		public KElementEnumerator(final int k) {
			this.k = k;
			
			this.numKSubsetElems = (int) numberOfKElements(k); 
			if (numKSubsetElems < 0) {
				throw new IllegalArgumentException("Subset too large.");
			}
			
			final SetEnumValue convert = set.toSetEnum();
			convert.normalize();
			elems = convert.elems;

			reset();
		}
		
		@Override
		public void reset() {
			index = (1 << k) - 1;
			cnt = 0;
		}

		// see "Compute the lexicographically next bit permutation" at
		// http://graphics.stanford.edu/~seander/bithacks.html#NextBitPermutation
		private int nextIndex() {
			final int oldIdx = this.index;

			final int t = (index | (index - 1)) + 1;
			this.index = t | ((((t & -t) / (index & -index)) >> 1) - 1);

			return oldIdx;
		}

		@Override
		public Value nextElement() {
			if (cnt >= numKSubsetElems) {
				return null;
			}
			cnt++;

			int bits = nextIndex();
			final ValueVec vals = new ValueVec(Integer.bitCount(bits));
			for (int i = 0; bits > 0 && i < elems.size(); i++) {
				// Treat bits as a bitset and add the element of elem at current
				// position i if the LSB of bits happens to be set.
				if ((bits & 0x1) > 0) {
					vals.addElement(elems.elementAt(i));
				}
				// ...right-shift zero-fill bits by one afterwards.
				bits = bits >>> 1;
			}
			return new SetEnumValue(vals, false);
		}
		
		public KElementEnumerator sort() {
			this.elems.sort(true);
			return this;
		}
	}
	
	@Override
	public ValueEnumeration elements(final Ordering ordering) {
		// Use elementsNormalized regardless of requested ordering. Even for ordering
		// UNDEFINED, elementsNormalized is fastest.
		return elements();
	}

  public final ValueEnumeration elements() {
    try {
      if (this.pset == null || this.pset == DummyEnum) {
    	  // See note on SetEnumValue#convert for SubsetValue wrt
    	  // the normalized SetEnumValue result.
    	  return elementsNormalized();
      }
      return this.pset.elements();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }
  
  final ValueEnumeration elementsLexicographic() {
      return new Enumerator();
  }

  final class Enumerator implements ValueEnumeration {
    private ValueVec elems;
    private BitSet descriptor;

    public Enumerator() {
    	//WARNING! Mutates the outer instance!?
      set = set.toSetEnum();
      set.normalize();
      this.elems = ((SetEnumValue)set).elems;
      this.descriptor = new BitSet(this.elems.size());
    }

    public final void reset() {
      this.descriptor = new BitSet(this.elems.size());
    }

    public final Value nextElement() {
      if (this.descriptor == null) return null;
      ValueVec vals = new ValueVec();
      int sz = this.elems.size();
      if (sz == 0) {
        this.descriptor = null;
      }
      else {
        for (int i = 0; i < sz; i++) {
          if (this.descriptor.get(i)) {
            vals.addElement(this.elems.elementAt(i));
          }
        }
        for (int i = 0; i < sz; i++) {
          if (this.descriptor.get(i)) {
            this.descriptor.clear(i);
            if (i >= sz - 1) {
              this.descriptor = null;
              break;
            }
          }
          else {
            this.descriptor.set(i);
            break;
          }
        }
      }
      return new SetEnumValue(vals, true);
    }

  }

	@Override
	public ValueEnumeration elements(final int k) {
		final int sz = this.set.size();

		// Use probabilistic CTSE if size of input set or k are too large. CoinTossing
		// can yield duplicates though, thus k means number of picks.
		if (sz >= 31 || k > (1 << 16)) {
			return new CoinTossingSubsetEnumerator(k);
		}
		return new SubsetEnumerator(k);
	}
	
	class SubsetEnumerator extends EnumerableValue.SubsetEnumerator {

		private final ValueVec elems;

		SubsetEnumerator(final int k) {
			super(k, 1 << set.size());
			final SetEnumValue convert = set.toSetEnum();
      		convert.normalize();
      		this.elems = convert.elems;
		}

		@Override
		public Value nextElement() {
			if (!hasNext()) {
				return null;
			}
			int bits = nextIndex();
			final ValueVec vals = new ValueVec(Integer.bitCount(bits));
			for (int i = 0; bits > 0 && i < this.elems.size(); i++) {
				// Treat bits as a bitset and add the element of this.elem at current
				// position i if the LSB of bits happens to be set.
				if ((bits & 0x1) > 0) {
					vals.addElement(this.elems.elementAt(i));
				}
				// ...right-shift zero-fill bits by one afterwards.
				bits = bits >>> 1;
			}
			return new SetEnumValue(vals, false);
		}
	}

	/*
	 * LL: I realized that efficiently choosing a random set of k elements in "SUBSET S"
	 * is simple. Just compute S and randomly choose k elements SS of SUBSET S by
	 * including each element of S in SS with probability 1/2.  This looks to me as
	 * if it's completely equivalent to enumerating all the elements of SUBSET S and
	 * choosing a random subset of those elements--except that if we want to choose
	 * exactly k elements, then we'll have to throw away duplicates.
	 */
	class CoinTossingSubsetEnumerator implements ValueEnumeration {

		private final ValueVec elems;
		private final double probability;
		private final int numOfPicks;
		private int i;

		public CoinTossingSubsetEnumerator(final int numOfPicks) {
			this(numOfPicks, .5d);
		}

		public CoinTossingSubsetEnumerator(final int numOfPicks, final double probability) {
			this.i = 0;
			this.numOfPicks = numOfPicks;
			this.probability = probability;

			final SetEnumValue convert = set.toSetEnum();
			convert.normalize();
			this.elems = convert.elems;
		}

		// Repeated invocation can yield duplicate elements due to the probabilistic
		// nature of CoinTossingSubsetEnumerator.
		public Value nextElement() {
			if (!hasNext()) {
				return null;
			}
			final ValueVec vals = new ValueVec(elems.size());
			for (int i = 0; i < elems.size(); i++) {
				if (EnumerableValue.getRandom().nextDouble() < probability) {
					vals.addElement(elems.elementAt(i));
				}
			}
			this.i++;
			return new SetEnumValue(vals, false);
		}

		private boolean hasNext() {
			return this.i < this.numOfPicks;
		}

		@Override
		public void reset() {
			this.i = 0;
		}

		int getNumOfPicks() {
			return numOfPicks;
		}
	}
}
