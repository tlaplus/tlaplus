/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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

import tlc2.TLCGlobals;
import tlc2.tool.FingerprintException;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Combinatorics;

public class KSubsetValue extends SubsetValue {

	private final int k;

	public KSubsetValue(int k, Value set) {
		super(set);
		this.k = k;
	}

	public KSubsetValue(int k, Value set, CostModel cm) {
		super(set, cm);
		this.k = k;
	}

	@Override
	public ValueEnumeration elements() {
		if (hasNoElements()) {
			return SetEnumValue.EmptySet.elements();
		}
		// Remember k as a member and return SubsetValue's kElement enumerator here.
		return kElements(k);
	}

	@Override
	public ValueEnumeration elements(Ordering ordering) {
		if (hasNoElements()) {
			return SetEnumValue.EmptySet.elements(ordering);
		}
		if (ordering == Ordering.RANDOMIZED) {
			return new RandomSubsetGenerator(k);
		}
		return super.elements(ordering);
	}

	private BigInteger count() {
		// THEOREM KSubsetNegativeEmpty == kSubset(-1, 1..3) = {}
		if (k < 0) {
			return BigInteger.ZERO;
		}
		// THEOREM KZeroBaseIndependent ==
		//   kSubset(0, 1..3) = kSubset(0, 1..4)
		if (k == 0) {
			return BigInteger.ONE;
		}
		final int n = this.set.size();
		if (k > n) {
			return BigInteger.ZERO;
		}
		return Combinatorics.bigChoose(n, Math.min(k, n - k));
	}

	@Override
	public final int size() {
		final BigInteger size = count();
        if (size.bitLength() > Integer.SIZE - 1) {
            throw new IllegalArgumentException(String.format("k=%s and n=%s", k, this.set.size()));
        }
        return size.intValue();
	}

	// THEOREM KSubsetTooLargeEmpty == kSubset(4, 1..3) = {}
	// THEOREM KSubsetNegativeEmpty == kSubset(-1, 1..3) = {}
	final boolean hasNoElements() {
		return this.k < 0 || (this.set.isFinite() && this.set.size() < this.k);
	}

	@Override
	public final boolean isFinite() {
		try {
			// THEOREM KZeroBaseIndependent ==
			//   kSubset(0, 1..3) = kSubset(0, 1..4)
			// THEOREM KSubsetNegativeEmpty == kSubset(-1, 1..3) = {}
			return this.k <= 0 || this.set.isFinite();
		} catch (RuntimeException | OutOfMemoryError e) {
			if (hasSource()) {
				throw FingerprintException.getNewHead(this, e);
			}
			throw e;
		}
	}

	// THEOREM KSubsetLargeDiffPowerSet ==
	//   kSubset(2, 1..64) # SUBSET (1..64)
	private Integer compareCardinality(SubsetValue other) {
		if (!this.set.isFinite() || !other.set.isFinite()) {
			return null;
		}
		return count().compareTo(BigInteger.ONE.shiftLeft(other.set.size()));
	}

	@Override
	public final boolean equals(Object obj) {
		try {
			if (obj instanceof KSubsetValue) {
				final KSubsetValue other = (KSubsetValue) obj;
				if (hasNoElements() || other.hasNoElements()) {
					return hasNoElements() && other.hasNoElements();
				}
				// THEOREM KZeroBaseIndependent ==
				//   kSubset(0, 1..3) = kSubset(0, 1..4)
				if (this.k == 0 && other.k == 0) {
					return true;
				}
				// THEOREM KOneDiffKTwo ==
				//   kSubset(1, 1..3) # kSubset(2, 1..3)
				return this.k == other.k && this.set.equals(other.set);
			}
			if (obj instanceof SubsetValue) {
				if (hasNoElements()) {
					return false;
				}
				final SubsetValue other = (SubsetValue) obj;
				final Integer cmp = compareCardinality(other);
				if (cmp != null && cmp != 0) {
					return false;
				}
				if (this.k == 0 && other.set.isEmpty()) {
					return true;
				}
			}
			super.convertAndCache();
			return this.pset.equals(obj);
		} catch (RuntimeException | OutOfMemoryError e) {
			if (hasSource()) {
				throw FingerprintException.getNewHead(this, e);
			}
			throw e;
		}
	}

	@Override
	public final int compareTo(Object obj) {
		try {
			if (obj instanceof KSubsetValue) {
				final KSubsetValue other = (KSubsetValue) obj;
				if (hasNoElements() || other.hasNoElements()) {
					if (hasNoElements() && other.hasNoElements()) {
						return 0;
					}
					return hasNoElements() ? -1 : 1;
				}
				if (this.k == other.k) {
					if (this.k == 0) {
						return 0;
					}
					return this.set.compareTo(other.set);
				}
				// THEOREM FPPairKTwoEightKOneFiveOrderIndependent ==
				//   TLCFP({kSubset(2, 1..8), kSubset(1, 1..5)}) =
				//     TLCFP({kSubset(1, 1..5), kSubset(2, 1..8)})
				if (this.set.isFinite() && other.set.isFinite()) {
					final int cmp = count().compareTo(other.count());
					if (cmp != 0) {
						return cmp;
					}
				}
				// THEOREM CardPairKZeroNatKOneNat ==
				//   Cardinality({kSubset(0, Nat), kSubset(1, Nat)}) = 2
				if (this.set.equals(other.set)) {
					return Integer.compare(this.k, other.k);
				}
				// THEOREM FPPairKThreeSixKOneTwentyOrderIndependent ==
				//   TLCFP({kSubset(3, 1..6), kSubset(1, 1..20)}) =
				//     TLCFP({kSubset(1, 1..20), kSubset(3, 1..6)})
			} else if (obj instanceof SubsetValue) {
				if (hasNoElements()) {
					return -1;
				}
				final SubsetValue other = (SubsetValue) obj;
				final Integer cmp = compareCardinality(other);
				if (cmp != null && cmp != 0) {
					return cmp;
				}
				if (this.k == 0 && other.set.isEmpty()) {
					return 0;
				}
			}
			super.convertAndCache();
			return this.pset.compareTo(obj);
		} catch (RuntimeException | OutOfMemoryError e) {
			if (hasSource()) {
				throw FingerprintException.getNewHead(this, e);
			}
			throw e;
		}
	}

	  @Override
	  public boolean member(Value val) {
		  // THEOREM ScalarNotInKSubsetNegative ==
		  //   1 \notin kSubset(-1, 1..3)
		  // THEOREM ScalarNotInKSubsetTooLarge ==
		  //   1 \notin kSubset(4, 1..3)
		  if (hasNoElements()) {
			  return false;
		  }
		  if (k == val.size()) {
			  return super.member(val);
		  }
		  return false;
	  }

	@Override
	public StringBuffer toString(StringBuffer sb, final int offset, final boolean swallow) {
		try {
			boolean expand = TLCGlobals.expand;
			try {
				if (expand) {
					expand = this.size() < 64;
				}
			} catch (Throwable e) {
				if (swallow) {
					expand = false;
				} else {
					throw e;
				}
			}

			if (expand) {
				if (this.size() == 0) {
					return sb.append("{}");
				}
				return this.toSetEnum().toString(sb, offset, swallow);
			}
			sb.append("{s \\in SUBSET (");
			this.set.toString(sb, offset, swallow);
			return sb.append(") : Cardinality(s) = ").append(k).append("}");
		} catch (RuntimeException | OutOfMemoryError e) {
			if (hasSource()) {
				throw FingerprintException.getNewHead(this, e);
			}
			throw e;
		}
	}
}