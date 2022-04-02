/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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

package tlc2.util;

import java.util.HashSet;

import tlc2.tool.Action;
import tlc2.tool.ModelChecker;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import util.Assert.TLCRuntimeException;

/**
 * A {@link SetOfStates} is a hash set with open addressing that is intended to
 * be used in TLC's {@link ModelChecker#getNextStates()} implementation. In this
 * are the number of {@link TLCState}s generated is relatively small and thus
 * the likelihood of consecutive ranges in the fingerprint domain low. In turn,
 * this means that the {@link TLCState}s in {@link SetOfStates} are evenly
 * distributed assuming the {@link SetOfStates#length} is sufficiently large.
 */
public final class SetOfStates {

	private TLCState[] states;
	private int count;
	private int length;
	private int thresh;

	public SetOfStates() {
		this(16);
	}

	public SetOfStates(final int size) {
		this.count = 0;
		this.length = size;
		this.thresh = length / 2;
		this.states = new TLCState[length];
	}

	public SetOfStates(final StateVec sv) {
		this(sv.size());
		for (int i = 0; i < sv.size(); i++) {
			put(sv.elementAt(i));
		}
	}

	public final void clear() {
		this.count = 0;
		this.states = new TLCState[length];
	}
	
	private final void grow() {
		final TLCState[] old = states;
		this.count = 0;
		this.length = 2 * this.length + 1;
		this.thresh = this.length / 2;
		this.states = new TLCState[this.length];
		for (int i = 0; i < old.length; i++) {
			final TLCState s = old[i];
			// This is where we have to redundantly compute the state's
			// fingerprint. Thus, try to minimize the number of grow operations.
			if (s != null) {
				this.put(s.fingerPrint(), s);
			}
		}
	}

	public final boolean put(final TLCState aState) {
		return put(aState.fingerPrint(), aState);
	}

	public final boolean put(final long fingerprint, final TLCState aState) {
		if (count >= thresh) {
			this.grow();
		}
		int loc = ((int) fingerprint & 0x7FFFFFFF) % this.length;
		// This loop keep going until either a match or a null bucket is found.
		while (true) {
			final TLCState ent = this.states[loc];
			if (ent == null) {
				states[loc] = aState;
				count++;
				return false;
			}
			// Compare with equals here to correctly handle symmetry where two
			// symmetric states will be hashed to neighboring buckets. The
			// assumption is that we will end up with only doing a few equality
			// checks because the primary comparison is still the fingerprint
			// and that the states[] is sparsely populated.
			try {
				// If this equals check is removed, the following tests will fail:
				// - pcal.FischerTest
			    // - tlc2.tool.SetOfStatesTest
			    // - tlc2.tool.liveness.BidirectionalTransitions1BxTest
			    // - tlc2.tool.liveness.BidirectionalTransitions1ByTest
			    // - tlc2.tool.liveness.BidirectionalTransitions1Test
			    // - tlc2.tool.liveness.CodePlexBug08EWD840FL1Test
			    // - tlc2.tool.liveness.CodePlexBug08EWD840FL2Test
			    // - tlc2.tool.liveness.CodePlexBug08EWD840FL3Test
			    // - tlc2.TLCTest
				if (aState.equals(ent)) {
					return true;
				}
			} catch (TLCRuntimeException e) {
				// Attempted to... appears in Value#equals and Value#compareTo.
				assert e.getMessage() != null && (e.getMessage().startsWith("Attempted to check equality of")
						|| e.getMessage().startsWith("Attempted to compare equality of"));
				// MAK 03/22/2021: 
				// The equals check above was added in 2.08 of 21 December 2015. It
				// has the (unintended) side-effect that it prevents users from
				// "mixing types" in the behavior part of the spec (this is rare)
				// when checking liveness properties:
				//   
				//   ...
				//   Next ==
				//     \/ x' \in 1..100
				//     \/ x' = TRUE
				//     \/ x' = "abc"
				//
				//   Prop ==
				//     <>[]TRUE \* Actual property doesn't matter.
				//
				// Instead, it can causes a hard-to-debug exception (iff there are
				// enough successor states to cause collisions above):
				//
				//   Error: TLC threw an unexpected exception.
				//   This was probably caused by an error in the spec or model.
				//   See the User Output or TLC Console for clues to what happened.
				//   The exception was a java.lang.RuntimeException
				//   : Attempted to check equality of string "" with non-string:
				//   FALSE
				//
				// The exception e indicates that the two states could not be compared
				// (equals) because value "types" are incompatible.  For example,
				// the value of variable x in ent is a BoolValue while it is StringValue
				// in aState. The exception e is useless to find the source location
				// because both TLCStates are fully generated and the source locations
				// are gone. 
				// It is unfortunate that TLC does type checking as a side-effect in its
				// Object#equals (and compareTo) method, which e.g. gets called when
				// TLCState instances or values are added to a java.util.Set.
			}
			loc = (loc + 1) % this.length;
		}
	}

	/**
	 * @return The current capacity of this set. [](capacity > size)
	 */
	public final int capacity() {
		return this.length;
	}
	
	/**
	 * @return The number of {@link TLCState}s in this set. [](capacity > size)
	 */
	public final int size() {
		return this.count;
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		final StringBuffer buf = new StringBuffer("{");
		for (int i = 0; i < states.length; i++) {
			final TLCState tlcState = states[i];
			if (tlcState != null) {
				buf.append("<<");
				buf.append(tlcState.fingerPrint());
				buf.append(",");
				final String toStr = tlcState.toString();
				buf.append(toStr.substring(0, toStr.length() - 1)); // chop off "\n"
				buf.append(">>,\n");
			}
		}
		buf.append("}");
		return buf.toString();
	}
	
	public java.util.Set<TLCState> getSubSet(final Action a) {
		final HashSet<TLCState> subset = new HashSet<>(size());
		
		for (int i = 0; i < size(); i++) {
			final TLCState next = next();
			// Deliberately use identify checking here! TLC maintains N instances of action
			// A, one for each N passed to A:
			//  
			//  A(n) == ...
			//  Next == \E n \in 1..N: A(n)
			//
			// Below, we want the TLCStates corresponding to A *and* a particular n! Equality
			// (equals) might not reflect this.
			if (a == next.getAction()) {
				subset.add(next);
			}
		}
		// Always clean-up after ourself!
		resetNext();
		
		return subset;
	}
	
	/*
	 * Iterate (avoids creating an iterator object at the price of the mandatory
	 * resetNext() method).
	 */

	private int iteratorIndex = 0;
	
	public final TLCState next() {
		TLCState next = null;
		while ((next = this.states[iteratorIndex++]) == null) {
			// No-op loop
		}
		return next;
	}

	public void resetNext() {
		iteratorIndex = 0;
	}
}
