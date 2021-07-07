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

import tlc2.tool.FingerprintException;
import tlc2.tool.coverage.CostModel;

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
		// Remember k as a member and return SubsetValue's kElement enumerator here.
		return kElements(k);
	}

	@Override
	public ValueEnumeration elements(Ordering ordering) {
		if (ordering == Ordering.RANDOMIZED) {
			return new RandomSubsetGenerator(k);
		}
		return super.elements(ordering);
	}
	
	@Override
	public final int size() {
		final long size = this.numberOfKElements(k);
        if ((int) size != size) {
            throw new IllegalArgumentException(String.format("k=%s and n=%s", k, size));
        }
        return (int) size;
	}
	
	  @Override
	  public final int compareTo(Object obj) {
	    try {
	      if (obj instanceof KSubsetValue) {
	    	  final KSubsetValue other = (KSubsetValue) obj;
	    	  if (this.k == other.k) {
	    		  return this.set.compareTo(other.set);
	    	  }
	    	  return Integer.compare(other.k, this.k); // order of parameters matters!
	      }
	      super.convertAndCache();
	      return this.pset.compareTo(obj);
	    }
	    catch (RuntimeException | OutOfMemoryError e) {
	      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
	      else { throw e; }
	    }
	  }

	  @Override
	  public boolean member(Value val) {
		  if (k == val.size()) {
			  return super.member(val);
		  }
		  return false;
	  }
}