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

import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.lamport.tla.toolbox.tool.tlc.launch.TraceExpressionInformationHolder;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.tool.tlc.model.ModelWriter;

/**
 * Representation of the TLC error
 * @author Simon Zambrovski
 */
public class TLCError
{
	public enum Length {
		ALL, RESTRICTED;
	}
	
	public enum Order {
		OneToN, NToOne;
		
		public static Order valueOf(final boolean b) {
			if (b) {
				return NToOne;
			}
			return OneToN;
		}
	}
	
    private String message = "";
    private LinkedList<TLCState> states = new LinkedList<TLCState>();
    private TLCError cause;
    private int errorCode;
	private int numberOfStatesToShow = Integer.MAX_VALUE; // no restriction by default
    /**
     * Sort order in which states are sorted in the variable viewer
     */
	private Order stateSortDirection;

	public TLCError() {
		this(Order.OneToN);
	}
	
	public TLCError(final Order order) {
		this.stateSortDirection = order;
	}
	
    /**
     * Add a state to a trace
     * @param state state to add
     */
    public void addState(TLCState state)
    {
        if (stateSortDirection == Order.NToOne) {
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
	
	public void removeStates(final List<TLCState> statesToRemove) {
		states.removeAll(statesToRemove);
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
		stateSortDirection = stateSortDirection == Order.OneToN ? Order.NToOne : Order.OneToN;
		Collections.reverse(states);
	}

	private void orderTrace(Order order) {
		if (stateSortDirection != order) {
			Collections.reverse(states);
			stateSortDirection = order;
		}
	}

	public String toSequenceOfRecords(final boolean includeHeaders) {
		final StringBuffer buf = new StringBuffer();
		buf.append(ModelWriter.BEGIN_TUPLE);
		buf.append(ModelWriter.CR);
		
		for (int i = 0; i < states.size(); i++) {
			final TLCState tlcState = states.get(i);
			if (tlcState.isBackToState() || tlcState.isStuttering()) {
				//TODO How to represent these two types of states?
				continue;
			}
			if (tlcState.getVariablesAsList().isEmpty() && includeHeaders == false) {
				// When an user has used filtering to hide all variables, the error trace here
				// has no variables. In this case just return empty sequence <<>> by breaking
				// from the loop.
				break;
			}
			
			if (i > 0) {
				// Append a comma if a record is going to be added below.
				buf.append(ModelWriter.COMMA).append(ModelWriter.CR);
			}
			buf.append(tlcState.asRecord(includeHeaders));
		}
			
		buf.append(ModelWriter.CR);
		buf.append(ModelWriter.END_TUPLE);
		return buf.toString();
	}

	public void applyFrom(final TLCError originalErrorWithTrace, final Map<String, Formula> traceExplorerExpressions,
			final Hashtable<String, TraceExpressionInformationHolder> traceExpressionDataTable,
			final String modelName) {

		// retrieve the original trace
		// this is necessary for items (3) and (5) from the list in the
		// documentation for this method
		List<TLCState> originalTrace = originalErrorWithTrace.getStates(Length.ALL);
		Assert.isNotNull(originalTrace, "Could not get original trace after running trace explorer. This is a bug.");

		// a comparator used for sorting the variables within each
		// state so that the variables representing the trace explorer
		// expressions appear first in each state
		final Comparator<TLCVariable> varComparator = new Comparator<TLCVariable>() {

			public int compare(TLCVariable var0, TLCVariable var1) {
				if ((var0.isTraceExplorerVar() && var1.isTraceExplorerVar())
						|| (!var0.isTraceExplorerVar() && !var1.isTraceExplorerVar())) {
					// both represent TE expressions or neither does
					// use string comparison to make sure
					// that the variables appear in the same order
					// in every state
					return var0.getName().compareTo(var1.getName());
				} else if (var0.isTraceExplorerVar()) {
					// var0 should appear before
					return -1;
				} else {
					// var1 represents TE expression, so it should appear before
					return 1;
				}
			}
		};

		final Order requestedOrder = originalErrorWithTrace.stateSortDirection;
		
		// Aligning both traces to the canonical order (OneToN) as precondition to the
		// code below which hasn't been written to support the NToOne order. The requested
		// order is applied at the end.
		this.orderTrace(Order.OneToN);
		originalErrorWithTrace.orderTrace(Order.OneToN);

		// found an error with a trace
		// this is the trace produced by the run
		// of TLC for the trace explorer
		List<TLCState> newTrace = this.getStates();

		Iterator<TLCState> newTraceIt = newTrace.iterator();
		Iterator<TLCState> originalTraceIt = originalTrace.iterator();

		TLCState currentStateNewTrace = newTraceIt.next();
		TLCState nextStateNewTrace = null;

		TLCState currentStateOriginalTrace = originalTraceIt.next();

		/*
		 * The following while loop performs items 1-4 for some of the states. In
		 * particular, if the original trace has n states and the trace produced by the
		 * trace explorer has m states, this loop performs items 1-4 for states 1
		 * through min(n-1, m-1). The trace produced by the trace explorer can be
		 * shorter than the original trace if there is a TLC error during evaluation of
		 * one of the states. The trace produced by the trace explorer can be longer
		 * than the original trace as in the example of item 5.
		 * 
		 * The final state of the trace produced by the trace explorer is processed
		 * after this loop. Item 5 is also accomplished after this loop.
		 */
		while (newTraceIt.hasNext() && originalTraceIt.hasNext()) {

			// change the label of the state of newTrace to the label of the state
			// of the original trace
			currentStateNewTrace.setLabel(currentStateOriginalTrace.getLabel());

			// set the location of the current state of the new trace
			currentStateNewTrace.setLocation(currentStateOriginalTrace.getModuleLocation());

			// need to get the next state in order to perform any
			// shifting of expression values (item 2 in the documentation)
			nextStateNewTrace = (TLCState) newTraceIt.next();

			TLCVariable[] currentStateNewTraceVariables = currentStateNewTrace.getVariables();
			TLCVariable[] nextStateNewTraceVariables = nextStateNewTrace.getVariables();

			applyFrom(traceExplorerExpressions, traceExpressionDataTable, nextStateNewTrace,
					currentStateNewTraceVariables, nextStateNewTraceVariables);

			// sort the variables so that the variables representing trace explorer
			// expressions appear first
			Arrays.sort(currentStateNewTraceVariables, varComparator);

			currentStateNewTrace = nextStateNewTrace;

			currentStateOriginalTrace = originalTraceIt.next();
		}

		/*
		 * Remove any extra states (item 5).
		 * 
		 * This is only necessary for looping or stuttering traces (n elements in
		 * original trace, m elements in new trace)- if (m >= n) remove states n..m else
		 * do nothing
		 * 
		 * if (m >= n), the new trace will be left with n-1 elements. Later code adds
		 * the final stuttering or "back to state" state to these traces.
		 * 
		 * There should never be extra states for non-looping, non-stuttering traces.
		 */
		if ((currentStateOriginalTrace.isBackToState() || currentStateOriginalTrace.isStuttering())
				&& newTrace.size() >= originalTrace.size()) {
			newTrace.subList(originalTrace.size() - 1, newTrace.size()).clear();
		}

		this.restrictTraceTo(originalErrorWithTrace.getTraceRestriction());

		// new trace should now be no longer than the original trace
		Assert.isTrue(newTrace.size() <= originalTrace.size(),
				"States from trace explorer trace not removed properly.");

		// fix the final state
		final TLCState finalStateOriginalTrace = (TLCState) originalTrace.get(originalTrace.size() - 1);

		if (newTrace.size() < originalTrace.size() - 1
				|| (!finalStateOriginalTrace.isStuttering() && !finalStateOriginalTrace.isBackToState())) {
			/*
			 * For a non-looping and non-stuttering state, just set the expressions with
			 * primed variables equal to "--" for the last state.
			 * 
			 * Do the same thing if the new trace is less than the original trace size minus
			 * 1. This means there was a TLC error before evaluating all of the states, so
			 * even if the original trace finished with a looping state or a stuttering
			 * state, the trace that is displayed to the user should not. It should
			 * terminate before the TLC error occurred.
			 */

			TLCState finalStateNewTrace = (TLCState) newTrace.get(newTrace.size() - 1);

			// state in the original trace at the same position as finalStateNewTrace
			TLCState samePositionOriginalTrace = (TLCState) originalTrace.get(newTrace.size() - 1);

			// set the label of the final state of the new trace
			finalStateNewTrace.setLabel(samePositionOriginalTrace.getLabel());

			// set the location of the final state of the new trace
			finalStateNewTrace.setLocation(samePositionOriginalTrace.getModuleLocation());

			TLCVariable[] finalStateNewTraceVariables = finalStateNewTrace.getVariables();

			// iterate through the variables
			for (int i = 0; i < finalStateNewTraceVariables.length; i++) {

				TraceExpressionInformationHolder traceExpressionData = traceExpressionDataTable
						.get(finalStateNewTraceVariables[i].getName().trim());

				if (traceExpressionData != null) {
					// we have located a trace expression variable

					if (traceExpressionData.getLevel() == 2) {
						// expression with primed variables
						// shift the value from the next state to the current state
						finalStateNewTraceVariables[i].setValue(TLCVariableValue.parseValue("\"--\""));
					}

					// set the name to be the expression the variable represents
					finalStateNewTraceVariables[i].setName(traceExpressionData.getExpression());
					// flag this as a variable representing a trace explorer expression
					finalStateNewTraceVariables[i].setTraceExplorerVar(true);
				}
			}

			// sort the variables of the final state
			Arrays.sort(finalStateNewTraceVariables, varComparator);
		} else if (finalStateOriginalTrace.isBackToState()) {
			this.addState(TLCState.BACK_TO_STATE(finalStateOriginalTrace.getStateNumber(), modelName));
		} else {
			// stuttering trace
			this.addState(TLCState.STUTTERING_STATE(finalStateOriginalTrace.getStateNumber(), modelName));
		}
		
		this.orderTrace(requestedOrder);
	}

	private void applyFrom(final Map<String, Formula> traceExplorerExpressions,
			final Hashtable<String, TraceExpressionInformationHolder> traceExpressionDataTable,
			TLCState nextStateNewTrace, TLCVariable[] currentStateNewTraceVariables,
			TLCVariable[] nextStateNewTraceVariables) {
		// iterate through the variables
		for (int i = 0; i < currentStateNewTraceVariables.length; i++) {
			// This code assumes that the variables are in the same order in each state
			String variableName = currentStateNewTraceVariables[i].getName();
			// if next state is back to state or stuttering, it has no variables, so the
			// code
			// contained within the if block would cause an NPE
			if (!nextStateNewTrace.isBackToState() && !nextStateNewTrace.isStuttering()) {
				Assert.isTrue(variableName.equals(nextStateNewTraceVariables[i].getName()),
						"Variables are not in the same order in each state. This is unexpected.");
			}

			// retrieve the object containing the data corresponding to the variable.
			// this object will be null if the variable currently being looked at does
			// not represent a trace explorer expression
			// If the variable does represent a trace explorer expression, then the
			// following
			// object will contain the variable name, the expression, and the level of the
			// expression
			TraceExpressionInformationHolder traceExpressionData = traceExpressionDataTable.get(variableName.trim());

			if (traceExpressionData != null) {
				// we have located a trace expression variable

				// If next state is back to state or stuttering, it has no variables, so the
				// code contained within this if block would not apply. It should be unnecessary
				// to check for this because the while loop should terminate before this
				// happens.
				if (!nextStateNewTrace.isBackToState() && !nextStateNewTrace.isStuttering()
						&& traceExpressionData.getLevel() == 2) {
					// found expression with primed variables
					// shift the value from the next state to the current state
					currentStateNewTraceVariables[i].setValue(nextStateNewTraceVariables[i].getValue());

				}

				// set the name to be the expression the variable represents
				currentStateNewTraceVariables[i].setName(traceExpressionData.getExpression());

				// flag this as a variable representing a trace explorer expression
				currentStateNewTraceVariables[i].setTraceExplorerVar(true);

				continue;
			}

			if (traceExplorerExpressions.containsKey(variableName.trim())) {
				currentStateNewTraceVariables[i].setTraceExplorerVar(true);
			}
		}
	}
	
	/**
	 * This clone includes clones of each TLCState held.
	 */
	@Override
	public TLCError clone() {
		final TLCError clone = new TLCError(stateSortDirection);
		
		clone.message = message;
		clone.cause = cause;
		clone.errorCode = errorCode;
		clone.numberOfStatesToShow =  numberOfStatesToShow;
		states.stream().forEach((state) -> clone.states.add(state.clone()));
		
		return clone;
	}
}
