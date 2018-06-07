// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 13:46:07 PST by lamport
//      modified on Fri Aug 10 15:10:16 PDT 2001 by yuanyu

package tlc2.value;

import java.util.BitSet;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.FingerprintException;
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
  
	public EnumerableValue getRandomSubsetSet(final int numOfPicks, final double probability) {
		final CoinTossingSubsetEnumerator enumerator = new CoinTossingSubsetEnumerator(numOfPicks, probability);
		
		int sum = 0;
		final ValueVec vec = new ValueVec(numOfPicks);
		Value val;
		while ((val = enumerator.nextElement()) != null) {
			sum += val.size();
			vec.addElement(val);
		}
		// Remove duplicates right away which also normalizes vec.
		vec.sort(true);
		
		// Tell user how many elements she actually gets. 		
		final int size = vec.size();
		if(numOfPicks > size) {
			final double average = (1d / vec.size()) * sum;
			MP.printWarning(EC.GENERAL, String.format("Requested RandomSubsetSet of size %s but only generated subset with %s unique elements (average element length is %02.0f).",
							numOfPicks, vec.size(), average));
		}
		
    	return new SetEnumValue(vec, true);
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
	public ValueEnumeration elements(final double fraction) {
		final int sz = this.set.size();

		final int k = calculateK(fraction, sz);
		
		// Use probabilistic CTSE if size of input set or k are too large. CoinTossing
		// can yield duplicates though, thus k means number of picks.
		if (sz >= 31 || k > (1 << 16)) {
			return new CoinTossingSubsetEnumerator(k);
		}
		return new SubsetEnumerator(fraction);
	}

	static int calculateK(final double fraction, final int n) {
		// Handle extreme/bogus input:
		if (n <= 0) {
			return 0;
		} else if (fraction >= 1.0 && n >= 31) {
			return Integer.MAX_VALUE;
		} else if (fraction >= 1.0) {
			return 1 << n; // 2^n
		} else if (fraction < 0 || fraction <= -0.0) {
			return 0;
		}
		
		// Calculate k without raising 2^sz which can get very large.
		int k;
		try {
			k = Math.toIntExact((long) Math.ceil(Math.pow(10, (n * Math.log10(2)) + Math.log10(fraction))));
			//assert k == Math.toIntExact(Math.round(Math.pow(2, n) * fraction));
		} catch (ArithmeticException e) {
			k = Integer.MAX_VALUE;
		}
		return k;
		
		// More readable but slower.
//		final BigDecimal subsetN = BigDecimal.valueOf(2).pow(n);
//		return subsetN.multiply(BigDecimal.valueOf(fraction)).intValue();
	}
	
	class SubsetEnumerator extends EnumerableValue.SubsetEnumerator {

		private final ValueVec elems;

		SubsetEnumerator(final int k) {
			super(k, 1 << set.size());
			final SetEnumValue convert = SetEnumValue.convert(set);
      		convert.normalize();
      		this.elems = convert.elems;
		}
		
		SubsetEnumerator(final double fraction) {
			super(fraction);
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
			for (int i = 0; i < this.elems.size(); i++) {
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
	
  	private static final double COIN_TOSS_BIAS = Double
			.valueOf(System.getProperty(SubsetValue.class.getName() + ".cointossbias", ".5d"));

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
			this(numOfPicks, COIN_TOSS_BIAS);
		}

		public CoinTossingSubsetEnumerator(final double probability) {
			this(Integer.MAX_VALUE, probability);
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
				if (EnumerableValue.RANDOM.nextDouble() < probability) {
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
