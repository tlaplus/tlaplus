// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:20:54 PST by lamport
//      modified on Thu Mar 11 21:25:20 PST 1999 by yuanyu

package tlc2.value.impl;

import tlc2.value.IValue;

public interface Enumerable extends IValue {

	enum Ordering {
		UNDEFINED,
		/**
		 * The normalized order is the order of elements when a Value gets
		 * fingerprinted (@see {@link Value#fingerPrint(long)}.
		 */
		NORMALIZED;
	}
	
  public int size();
  public boolean member(Value elem);
  /**
   * Semantics or Enumerable#elements(Ordering#UNDEFINED) 
   */
  public ValueEnumeration elements();
  public ValueEnumeration elements(final Ordering ordering);
  /**
   * Returns a {@link ValueEnumeration} which returns k 
   * {@link IValue}s of all {@link IValue}s returned by 
   * {@link Enumerable#elements()}. In other words, it returns
   * a randomly chosen subset of all {@link IValue} members of
   * this {@link Enumerable}.
   */
  public ValueEnumeration elements(final int k);
  public EnumerableValue getRandomSubset(final int k);
  public Value isSubsetEq(Value other);
}

