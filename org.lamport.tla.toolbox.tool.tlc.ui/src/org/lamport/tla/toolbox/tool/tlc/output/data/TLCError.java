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
 *   Simon Zambrovski - initial API and implementation
 ******************************************************************************/

package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

/**
 * Representation of the TLC error
 * @author Simon Zambrovski
 */
public class TLCError
{
	public enum Length {
		ALL, RESTRICTED;
	}
	
    private String message = "";
    private LinkedList<TLCState> states = new LinkedList<TLCState>();
    private TLCError cause;
    private int errorCode;
	private int numberOfStatesToShow = Integer.MAX_VALUE; // no restriction by default

    /**
     * Add a state to a trace
     * @param state state to add
     */
    public void addState(TLCState state, boolean stateSortDirection)
    {
        if (stateSortDirection) {
        	states.addFirst(state);
        } else {
        	states.add(state);
        }
    }

    /**
     * Retrieves a cause of this error (or null if not a chained error)
     * @return the causing error
     */
    public final TLCError getCause()
    {
        return cause;
    }

    public final void setCause(TLCError cause)
    {
        this.cause = cause;
    }

    public final String getMessage()
    {
        return message;
    }

	public void restrictTraceTo(int numberOfStatesToShow) {
		this.numberOfStatesToShow = numberOfStatesToShow;
	}
	
	public boolean isTraceRestricted() {
		return this.states.size() > this.numberOfStatesToShow;
	}
	
	/**
	 * @return The amount of trace states currently hidden because of the
	 *         restriction.
	 */
	public int getNumberOfRestrictedTraceStates() {
		if (isTraceRestricted()) {
			return this.states.size() - this.numberOfStatesToShow;
		} else {
			return 0;
		}
	}

	public int getTraceRestriction() {
		return this.numberOfStatesToShow;
	}
	
	public void reduceTraceRestrictionBy(int numberOfStatesToShow) {
		this.numberOfStatesToShow += numberOfStatesToShow;
	}

	public int getTraceSize(final int level) {
		if (states.isEmpty()) {
			return 0;
		}
		
		TLCState representative = this.states.getFirst();
		if (representative.isInitialState()) {
			representative = states.getLast();
		}
		final int varCnt = representative.getVariableCount(level);
		
		if (numberOfStatesToShow < states.size()) {
			return numberOfStatesToShow * (varCnt + 1);
		}
		return states.size() * (varCnt + 1);
	}
	
	public int getTraceSize() {
		return getTraceSize(0);
	}
	
	public final List<TLCState> getStates() {
		return getStates(Length.RESTRICTED);
	}

	/**
	 * Returns the {@link TLCState}s that represent the trace of this
	 * {@link TLCError}. If {@link Length#ALL} is given, all {@link TLCState}s
	 * are returned regardless of any restriction imposed. Length.RESTRICTED
	 * returns the subList of states according to the restriction set.
	 * 
	 * @param l
	 * @return
	 */
	public final List<TLCState> getStates(Length l) {
		if (l == Length.ALL) {
			return states;
		}
		if (states.size() > numberOfStatesToShow) {
			// If only a sublist is requested, the current order of the list has
			// to be taken into account. Otherwise, reversing the tree's sort
			// order with a subList input will alternate between the states' 
			// head and tail.
			// I.e. the tree starts with the state's tail. The user then changes
			// the sort order which triggers a call to getStates again. However,
			// because the underlying states list had been reversed in the
			// meantime, it now returns the head.
			if (states.getFirst().isInitialState()) {
				// If the first state is the initial state, the list is sorted in
				// ascending order. Thus, return the states' tail. Otherwise, head.
				return states.subList(states.size() - numberOfStatesToShow, states.size());
			}
			return states.subList(0, numberOfStatesToShow);
		}
		return states;
	}

	public boolean isTraceEmpty() {
		return numberOfStatesToShow == 0 || states.isEmpty();
	}

    public final int getErrorCode()
    {
        return errorCode;
    }

    public final void setErrorCode(int errorCode)
    {
        this.errorCode = errorCode;
    }

    public void setMessage(String message)
    {
        this.message = message;
    }

    public boolean hasTrace()
    {
        return this.states != null && !this.states.isEmpty();
    }
    
	public void reverseTrace() {
		Collections.reverse(states);
	}
}
