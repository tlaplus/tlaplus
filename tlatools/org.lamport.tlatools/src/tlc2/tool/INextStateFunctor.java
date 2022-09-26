/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
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
package tlc2.tool;

import tlc2.util.SetOfStates;

public interface INextStateFunctor extends IStateFunctor {
	
	public static class InvariantViolatedException extends StatefulRuntimeException {
		public InvariantViolatedException() {
			super("Invariant violated");
		}
	}

	Object addElement(final TLCState s, final Action a, final TLCState t);

	default Object addElement(final TLCState state) {
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Contrary to {@link INextStateFunctor#addElement(TLCState)} and
	 * {@link INextStateFunctor#addElement(TLCState, Action, TLCState)}, replaces
	 * the previously added elements (TLCStates) with this one. Implementations do
	 * <i>not</i> check that TLCState <code>state</code> violates invariants, state-
	 * or action-constraints, ... (to check properties, ..., call addElement first).
	 */
	default Object setElement(final TLCState state) {
		throw new UnsupportedOperationException();
	}

	default boolean hasStates() {
		throw new UnsupportedOperationException();
	}
	
	default SetOfStates getStates() {
		return new SetOfStates(0);
	}
}
