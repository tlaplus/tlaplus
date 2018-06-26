// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 13:46:07 PST by lamport
//      modified on Fri Aug 10 15:10:16 PDT 2001 by yuanyu

package tlc2.value;

import java.util.BitSet;
import java.util.Collection;
import java.util.HashSet;

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
          if (!this.set.member(elem)) return false;
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

  public final void normalize() {
    try {
      if (this.pset == null || this.pset == DummyEnum) {
        this.set.normalize();
      }
      else {
        this.pset.normalize();
      }
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
      this.pset = SetEnumValue.convert(this);
    }
    else if (this.pset == DummyEnum) {
      SetEnumValue val = null;
      synchronized(this) {
        if (this.pset == DummyEnum) {
          val = SetEnumValue.convert(this);
          val.deepNormalize();
        }
      }
      synchronized(this) {
        if (this.pset == DummyEnum) { this.pset = val; }
      }
    }
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
        Value val = SetEnumValue.convert(this);
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
			return new ValueEnumeration() {
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
			
			final SetEnumValue convert = SetEnumValue.convert(set);
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

  public final ValueEnumeration elements() {
    try {
      if (this.pset == null || this.pset == DummyEnum) {
        return new Enumerator();
      }
      return this.pset.elements();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  final class Enumerator implements ValueEnumeration {
    private ValueVec elems;
    private BitSet descriptor;

    public Enumerator() {
    	//WARNING! Mutates the outer instance!?
      set = SetEnumValue.convert(set);
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
			final SetEnumValue convert = SetEnumValue.convert(set);
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

			final SetEnumValue convert = SetEnumValue.convert(set);
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
