// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2021, Oracle and/or its affiliates.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 13:46:07 PST by lamport
//      modified on Fri Aug 10 15:10:16 PDT 2001 by yuanyu

package tlc2.value.impl;

import java.io.IOException;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.BitSet;
import java.util.Collection;
import java.util.HashSet;
import java.util.Random;
import java.util.TreeMap;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.tool.FingerprintException;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Combinatorics;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueOutputStream;
import tlc2.value.RandomEnumerableValues;
import tlc2.value.Values;
import util.Assert;
import util.TLAConstants;

public class SubsetValue extends EnumerableValue implements Enumerable {
  public Value  set;           // SUBSET set
  protected SetEnumValue pset;

  /* Constructor */
  public SubsetValue(Value  set) {
    this.set = set;
    this.pset = null;
  }

  public SubsetValue(Value  set, CostModel cm) {
	  this(set);
	  this.cm = cm;
  }

  @Override
  public final byte getKind() { return SUBSETVALUE; }

  @Override
  public int compareTo(Object obj) {
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

  public boolean equals(Object obj) {
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

  @Override
  public boolean member(Value val) {
    try {
      if (val instanceof Enumerable) {
        ValueEnumeration Enum = ((Enumerable)val).elements();
        Value  elem;
        while ((elem = Enum.nextElement()) != null) {
          if (!this.set.member(elem)) {
        	  return false;
          }
        }
      }
      else {
        Assert.fail("Attempted to check if the non-enumerable value\n" +
        Values.ppr(val.toString()) + "\nis element of\n" + Values.ppr(this.toString()), getSource());
      }
      return true;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public Value isSubsetEq(Value other) {
    try {
      // Reduce (SUBSET A \subseteq SUBSET B) to (A \subseteq B) to avoid
      // exponential blowup inherent in generating the power set.
	  // For KSubsetValue, delegate to the naive implementation that enumerates the
	  // elements. In other words, don't rewrite if a KSubsetValue is involved.
	  if (other instanceof SubsetValue && !(other instanceof KSubsetValue) && this.set instanceof Enumerable) {
        final SubsetValue sv = (SubsetValue) other;
        return ((Enumerable) this.set).isSubsetEq(sv.set);
      }
      return super.isSubsetEq(other);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isFinite() {
    try {
      return this.set.isFinite();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value takeExcept(ValueExcept ex) {
    try {
      if (ex.idx < ex.path.length) {
        Assert.fail("Attempted to apply EXCEPT to the set " + Values.ppr(this.toString()) + ".", getSource());
      }
      return ex.value;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value takeExcept(ValueExcept[] exs) {
    try {
      if (exs.length != 0) {
        Assert.fail("Attempted to apply EXCEPT to the set " + Values.ppr(this.toString()) + ".", getSource());
      }
      return this;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public int size() {
    try {
      int sz = this.set.size();
      if (sz >= 31) {
        Assert.fail(EC.TLC_MODULE_OVERFLOW, "the number of elements in:\n" +
        Values.ppr(this.toString()));
      }
      return (1 << sz);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isNormalized() {
    try {
      return (this.pset != null &&
        this.pset != SetEnumValue.DummyEnum &&
        this.pset.isNormalized());
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value normalize() {
    try {
      if (this.pset == null || this.pset == SetEnumValue.DummyEnum) {
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

  @Override
  public final void deepNormalize() {
	    try {
      set.deepNormalize();
      if (pset == null) {
        pset = SetEnumValue.DummyEnum;
      }
      else if (pset != SetEnumValue.DummyEnum) {
        pset.deepNormalize();
      }
	    }
	    catch (RuntimeException | OutOfMemoryError e) {
	      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
	      else { throw e; }
	    }
  }

  @Override
  public final boolean isDefined() {
    try {
      return this.set.isDefined();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final IValue deepCopy() { return this; }

  @Override
  public final boolean assignable(Value val) {
    try {
      return this.equals(val);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

	@Override
	public final void write(final IValueOutputStream vos) throws IOException {
		pset.write(vos);
	}

  /* The fingerprint  */
  @Override
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

  @Override
  public final IValue permute(IMVPerm perm) {
    try {
      this.convertAndCache();
      return this.pset.permute(perm);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  protected final void convertAndCache() {
    if (this.pset == null) {
      this.pset = (SetEnumValue) this.toSetEnum();
    }
    else if (this.pset == SetEnumValue.DummyEnum) {
      SetEnumValue val = (SetEnumValue) this.toSetEnum();
      val.deepNormalize();
      this.pset = val;
    }
  }

  @Override
  public final Value toSetEnum() {
      if (this.pset != null && this.pset != SetEnumValue.DummyEnum) {
        return this.pset;
      }
      ValueVec vals = new ValueVec(this.size());
      ValueEnumeration Enum = this.elements();
      Value  elem;
      while ((elem = Enum.nextElement()) != null) {
        vals.addElement(elem);
      }
      // For as long as pset.elements() (SubsetValue#elements)
      // internally calls SubsetValue#elementsNormalized, the
      // result SetEnumValue here is indeed normalized.
      if (coverage) {cm.incSecondary(vals.size());}
      return new SetEnumValue(vals, true, cm);
  }

  /* The string representation  */
  @Override
  public final StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
    try {
      boolean unlazy = TLCGlobals.expand;
      try {
        if (unlazy) {
          unlazy = this.set.size() < 7;
        }
      }
      catch (Throwable e) { if (swallow) unlazy = false; else throw e; }

      if (unlazy) {
        Value  val = this.toSetEnum();
        return val.toString(sb, offset, swallow);
      }
      else {
        sb = sb.append("SUBSET ");
        if (this.set instanceof IntervalValue) {
        	// MAK 07/2021:
			// SUBSET has higher precedence than the .. (infix) operator appearing in
			// interval definitions (see tla2sany.semantic.BuiltInLevel). Thus, printing
        	//   SUBSET 1..2
        	// is wrong because its meaning is
        	//   ((SUBSET 1)..2)
        	//
        	// We can correct this easily here by adding parenthesis:
        	//   SUBSET (1..2)
        	//   SUBSET (1+2..42)
        	sb.append(TLAConstants.L_PAREN);
        	sb = this.set.toString(sb, offset, swallow);
        	sb.append(TLAConstants.R_PAREN);
        } else {
        	sb = this.set.toString(sb, offset, swallow);
        }
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
		final SetEnumValue convert = (SetEnumValue) set.toSetEnum();
		convert.normalize();
		final ValueVec elems = convert.elems;

		return new Unrank(kSubset, Combinatorics.bigSumChoose(elems.size(), kSubset).longValueExact(),
				Combinatorics.pascalTableUpTo(elems.size(), kSubset), elems, kSubset);
  	}
 
	public Enumerable getRandomSetOfSubsets(final int numOfSubsetsRequested, final int maxLengthOfSubsets) {
		// Convert outer set only once.
		final SetEnumValue convert = (SetEnumValue) set.toSetEnum();
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
							RandomEnumerableValues.get());

			Value  subset;
			while ((subset = unrank.randomSubset()) != null && vec.size() < numOfSubsetsRequested) {
				vec.addElement(subset);
			}
		}
		assert vec.size() == numOfSubsetsRequested;
		return new SetEnumValue(vec, false, cm);
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
			return new SetEnumValue(vec, false, cm);
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

		public Value  randomSubset() {
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
		final Collection<Value > sets = new HashSet<>(estimated);
		Value  val;
		while ((val = enumerator.nextElement()) != null) {
			sets.add(val);
		}
		
		return new SetEnumValue(new ValueVec(sets), false, cm);
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
			return new SetEnumValue(cm);
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
		final Value setEnum = set.toSetEnum();
		if (setEnum == null) {
			// E.g. SUBSET <<1,2>> or SUBSET [ a |-> 42]
            Assert.fail("Attempted to compute the value of an expression of form\n" +
                    "SUBSET S, but S is a non-enumerable value:\n" + Values.ppr(this.set), getSource());
		}
		final ValueVec elems = ((SetEnumValue) setEnum.normalize()).elems;
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
					return new SetEnumValue(cm);
				}

				final ValueVec vals = new ValueVec(k);
				int i = k - 1;
				for (int j = i; j >= 0; j--) {
					vals.addElementAt(elems.elementAt(indices[j]), j);
					if (indices[j] + k - j == n) {
						i = j - 1;
					}
				}
				final SetEnumValue result = new SetEnumValue(vals, true, cm);
				
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
		if (k < 0 || size < k || size > 63) {
			// Size >63 because KElementEnumerator.nextElement() limited to 63 bits
			// (assert vals.size() == k will be violated).
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
		
		private long index;
		private int cnt;

		public KElementEnumerator(final int k) {
			this.k = k;
			
			this.numKSubsetElems = (int) numberOfKElements(k); 
			if (numKSubsetElems < 0) {
				throw new IllegalArgumentException("Subset too large.");
			}
			
			final SetEnumValue convert = (SetEnumValue) set.toSetEnum();
			convert.normalize();
			elems = convert.elems;

			reset();
		}
		
		@Override
		public void reset() {
			index = (1L << k) - 1L;
			cnt = 0;
		}

		// see "Compute the lexicographically next bit permutation" at
		// http://graphics.stanford.edu/~seander/bithacks.html#NextBitPermutation
		private long nextIndex() {
			final long oldIdx = this.index;

			final long t = (index | (index - 1L)) + 1L;
			this.index = t | ((((t & -t) / (index & -index)) >> 1L) - 1L);

			return oldIdx;
		}

		@Override
		public Value nextElement() {
			if (cnt >= numKSubsetElems) {
				return null;
			}
			cnt++;

			long bits = nextIndex();
			final ValueVec vals = new ValueVec(Long.bitCount(bits));
			for (int i = 0; bits > 0 && i < elems.size(); i++) {
				// Treat bits as a bitset and add the element of elem at current
				// position i if the LSB of bits happens to be set.
				if ((bits & 0x1) > 0) {
					vals.addElement(elems.elementAt(i));
				}
				// ...right-shift zero-fill bits by one afterwards.
				bits = bits >>> 1;
			}
			assert vals.size() == k;
			return new SetEnumValue(vals, false, cm);
		}
		
		public KElementEnumerator sort() {
			this.elems.sort(true);
			return this;
		}
		
		@Override
		public SetEnumValue asSet() {
			final ValueVec vv = new ValueVec(numKSubsetElems);
			Value elem;
			while ((elem = nextElement()) != null) {
				vv.addElement(elem);
			}
			return new SetEnumValue(vv, false);
		}
	}

	public final Value kSubset(int k) {
		return kElements(k).asSet();
	}
	
	@Override
	public ValueEnumeration elements(final Ordering ordering) {
		if (ordering == Ordering.RANDOMIZED) {
			return ((SetEnumValue) toSetEnum()).elements(ordering);
		}
		// Use elementsNormalized regardless of requested ordering. Even for ordering
		// UNDEFINED, elementsNormalized is fastest.
		return elements();
	}

  @Override
  public ValueEnumeration elements() {
    try {
      if (this.pset == null || this.pset == SetEnumValue.DummyEnum) {
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

    @Override
    public final void reset() {
      this.descriptor = new BitSet(this.elems.size());
    }

    @Override
    public final Value nextElement() {
			if (this.descriptor == null)
				return null;
			ValueVec vals;
			int sz = this.elems.size();
			if (sz == 0) {
				vals = new ValueVec(0);
				this.descriptor = null;
			} else {
				vals = new ValueVec(this.descriptor.cardinality());
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
					} else {
						this.descriptor.set(i);
						break;
					}
				}
			}
	    	  if (coverage) { cm.incSecondary(vals.size()); }
			return new SetEnumValue(vals, true, cm);
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
			final SetEnumValue convert = (SetEnumValue) set.toSetEnum();
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
			return new SetEnumValue(vals, false, cm);
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

			final SetEnumValue convert = (SetEnumValue) set.toSetEnum();
			convert.normalize();
			this.elems = convert.elems;
		}

		// Repeated invocation can yield duplicate elements due to the probabilistic
		// nature of CoinTossingSubsetEnumerator.
		@Override
        public Value nextElement() {
			if (!hasNext()) {
				return null;
			}
			final ValueVec vals = new ValueVec(elems.size());
			for (int i = 0; i < elems.size(); i++) {
				if (RandomEnumerableValues.get().nextDouble() < probability) {
					vals.addElement(elems.elementAt(i));
				}
			}
			this.i++;
			return new SetEnumValue(vals, false, cm);
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

	// This enumerator violates the expected behavior of ValueEnumeration to
	// terminate once all elements have been enumerated, which implies that it also
	// returns duplicates.  Its advantage over the other, stateful enumerators -that
	// guarantee termination- is that it is very cheap.  If we ever need this, a
	// terminating enumerator can be implemented with SubsetValue#getUnrank combined
	// with EnumerableValue.SubsetValueEnumerator, i.e. optimally parameterizing an
	// LCG with period m = NcK (n choose k) where NcK = n!/k!(n-k)! to pseudo-randomly
	// generate all values (indices) in the range [0, NcK)) and generating the 
	// subset for each index with Unrank#subsetAt.
	// ASSUME tlc2.tool.impl.Tool.PROBABILISTIC = TRUE
	public class RandomSubsetGenerator implements ValueEnumeration {
		
		private final int k;
		private final Random random;
		private final SetEnumValue s;
		private int n;

		public RandomSubsetGenerator(final int k) {
			this.k = k;
			
			this.s = (SetEnumValue) set.toSetEnum();
			this.s.normalize();
			this.n = this.s.elems.size();

			if (k < 0 || k > n) {
				throw new IllegalArgumentException(String.format("k=%s and n=%s", k, n));
			}
			
			this.random = RandomEnumerableValues.get();
		}
		
		@Override
		public void reset() {
			// This enumerator is stateless and, thus, reset is a no-op.
		}

		@Override
		public Value nextElement() {
			// This is Algorithm S introduced in volume 2 "Seminumerical Algorithms" in
			// Knuth's TAOCP. It iterates over the elements in S once while gradually
			// increasing the probability p of including an element at the current index
			// in the result. Compare with reservoir sampling discussed in section 3.4.2 of
			// TAOCP.
			// For more sophisticated algorithms see:
			// https://dl.acm.org/doi/10.1145/358105.893
			// https://dl.acm.org/doi/10.1145/23002.23003
			// https://dl.acm.org/doi/10.1145/3147.3165

			final ValueVec vec = new ValueVec(k);

            for (int t = 0; t < n; t++) {
				final double p = (k - vec.size()) / ((n - t) * 1d);

				if (random.nextDouble() <= p) {
					vec.addElement(s.elems.elementAt(t));
				}
				
				if (vec.size() == k) {
					break;
				}
			}

			// This variant reduces the number of calls to the random number generator by
			// allocating a bit set to remember the previously drawn elements.
//			final BitSet bs = new BitSet(n);
//			while (vec.size() < k) {
//				final int i = random.nextInt(n);
//				if (!bs.get(i)) {
//					bs.set(i);
//					vec.addElement(s.elems.elementAt(i));
//				}
//			}

			// This assertion holds because even with an imaginary Random#nextDouble that
			// returns 1 the probability p of the last k values will be 1.
            assert vec.size() == k;
			return new SetEnumValue(vec, false);
		}
	}
}
