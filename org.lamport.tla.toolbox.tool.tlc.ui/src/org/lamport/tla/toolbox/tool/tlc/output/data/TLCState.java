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

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import org.lamport.tla.toolbox.tool.tlc.ui.util.IModuleLocatable;

import tla2sany.st.Location;

/**
 * Representation of the TLC state
 * @author Simon Zambrovski
 */
public class TLCState implements IModuleLocatable
{
    private static final String COLON = ":";
    private static final String CR = "\n";
    private static final String STUTTERING = "Stuttering";
    private static final String AND = "/\\";
    private static final String EQ = " = ";
    private static final String BACK_TO_STATE = "Back";

    /**
     * A factory for stuttering states
     * @param modelName the name of the model for which this is a state
     */
    protected static TLCState STUTTERING_STATE(int number, String modelName)
    {
        TLCState state = new TLCState(number, modelName);
        state.stuttering = true;
        return state;
    }

    /**
     * A factory for Back to state states
     * @param modelName the name of the model for which this is a state
     * @param number2
     * @return
     */
    protected static TLCState BACK_TO_STATE(int number, String modelName)
    {
        TLCState state = new TLCState(number, modelName);
        state.isBackToState = true;
        return state;
    }

    /**
     * Parses the state information
     * @param input
     * @param modelName the name of the model for which this is a state
     * @return
     */
    public static TLCState parseState(String input, String modelName)
    {
        // state number
        int index = input.indexOf(COLON);
        // multi line
        int index2 = input.indexOf(CR, index);
        if (index2 == -1)
        {
            index2 = input.length();
        }

        int number = Integer.parseInt(input.substring(0, index));
        String label = input.substring(index + 1, index2);
        if (label.indexOf(STUTTERING) != -1)
        {
            return STUTTERING_STATE(number, modelName);
        } else if (label.indexOf(BACK_TO_STATE) != -1)
        {
            final TLCState state = BACK_TO_STATE(number, modelName);
            // See in MP.java case for EC.TLC_BACK_TO_STATE
            state.setLocation(Location.parseLocation(label.substring(" Back to State: ".length(), label.length()))); 
			return state;
        } else
        {
            TLCState state = new TLCState(number, modelName);
            state.label = label;
            state.variablesAsString = input.substring(index2 + 1);
            state.variables = TLCState.parseVariables(state.variablesAsString);
            state.setLocation(Location.parseLocation(label));
            return state;
        }
    }

    /**
     * Parse the state variables out of the state output
     * @param variablesText
     * @return
     */
	private static List<TLCVariable> parseVariables(String variablesText) {
        String[] lines = variablesText.split(CR);
		List<TLCVariable> vars = new ArrayList<TLCVariable>();
        int index;

        // buffer for accumulating the state variable
        String[] stateVarString = null;

        // iterate line-wise
        for (int j = 0; j < lines.length; j++)
        {
            // find the index of the first /\ in the line
            index = lines[j].indexOf(AND);

            // adding the current line to the previous lines
            if (index != -1)
            {
                // there was something in the buffer for the state variable
                // found an empty line, which means that this is the end of the current state
                if (stateVarString != null)
                {
                    TLCVariable var = new TLCVariable(stateVarString[0], TLCVariableValue.parseValue(stateVarString[1]));
                    vars.add(var);
                }

                stateVarString = lines[j].substring(index + AND.length()).split(EQ);
            } else
            {
                // no index

                if (stateVarString != null)
                {
                    // either an empty line
                    stateVarString[1] += CR;
                    stateVarString[1] += lines[j];
                } else
                {
                    // the state has one variable only
                    stateVarString = lines[j].split(EQ);
                }
            }
        }

        // write the last one
        if (stateVarString != null)
        {
            TLCVariable var = new TLCVariable(stateVarString[0], TLCVariableValue.parseValue(stateVarString[1]));
            vars.add(var);
        }

		Collections.sort(vars, new Comparator<TLCVariable>() {
			public int compare(TLCVariable v1, TLCVariable v2) {
				if (v1.isTraceExplorerVar() && v2.isTraceExplorerVar()) {
					// both are variables. Compare the vars alphabetically.
					return v1.getName().compareTo(v2.getName());
				}
				if (v1.isTraceExplorerVar()) {
					return -1;
				}
				if (v2.isTraceExplorerVar()) {
					return 1;
				}
				return v1.getName().compareTo(v2.getName());
			}
		});
		return vars;
    }

    private int number;
    private boolean stuttering = false;
    private boolean isBackToState = false;
    private String label;
    private String variablesAsString;
	private List<TLCVariable> variables = new ArrayList<TLCVariable>(0);
    /**
     * Contains the location of the action
     * which caused this state
     */
    private Location location;
    /**
     * The name of the model for which this
     * is a state.
     */
	private final String modelName;
	private boolean wasDiffed= false;

    /**
     * 
     * @param number the 1-based index of this state in the trace
     * @param modelName the name of the model for which this is a state
     */
    public TLCState(int number, String modelName)
    {
        this.number = number;
        this.modelName = modelName;
    }

    public boolean isStuttering()
    {
        return stuttering;
    }

    public boolean isBackToState()
    {
        return isBackToState;
    }
    
    public boolean isInitialState() {
    	return number == 1;
    }

	public boolean isExpandable() {
    	return !isBackToState() && !isStuttering();
	}

    public int getStateNumber()
    {
        return number;
    }

    public final String getLabel()
    {
        return label;
    }

    public void setLabel(String label)
    {
        this.label = label;
    }

	public final List<TLCVariable> getVariablesAsList() {
		return this.variables;
	}

	public final TLCVariable[] getVariables() {
		return variables.toArray(new TLCVariable[variables.size()]);
    }

    public String toString()
    {
        return variablesAsString;
    }

    public void setLocation(Location location)
    {
        this.location = location;
    }

    public Location getModuleLocation()
    {
        return location;
    }

    /**
     * Returns a string describing the state with the
     * variables representing trace explorer expressions
     * replaced with the expressions.
     * 
     * @return
     */
    public String getDescriptionWithTraceExpressions()
    {
        /*
         * The returns a conjunction list of variables.
         * 
         * For variables representing trace explorer expressions,
         * the returned string has:
         * 
         * /\ expr = value
         * 
         *  where expr is the single line form of the trace explorer expression
         *  as shown in the Name column of the trace viewer.
         *  
         *  For all other variables, this method attempts to display them as TLC
         *  does.
         */
        StringBuffer result = new StringBuffer();
		for (int i = 0; i < variables.size(); i++) {
			TLCVariable var = variables.get(i);
            result.append("/\\ ");
            if (var.isTraceExplorerVar())
            {
                result.append(var.getSingleLineName());
            } else
            {
                result.append(var.getName());
            }

            result.append(" = ");

            if (var.getValue().toString() != null)
            {
                result.append(var.getValue().toString());
            } else
            {
                result.append(var.getValue().toSimpleString());
            }

            result.append("\n");

        }
        return result.toString();
    }

    public String getModelName()
    {
        return modelName;
    }

    /**
     * Set the data structures that cause highlighting of changes in the
     * error trace.
     */
	public void diff(final TLCState other) {
		if (this == other || wasDiffed || other.isStuttering() || other.isBackToState()) {
			// there are no variables in other
			// because it is a stuttering or a back to state
			// step
			return;
		}
		wasDiffed = true;
		final List<TLCVariable> predecessorVariables = this.getVariablesAsList();
		final List<TLCVariable> secondVariables = other.getVariablesAsList();
		for (int i = 0; i < predecessorVariables.size(); i++) {
			final TLCVariableValue firstValue = predecessorVariables.get(i).getValue();
			final TLCVariableValue secondValue = secondVariables.get(i).getValue();
			firstValue.diff(secondValue);
		}
	}

	public int getVariableCount(int level) {
		if (level > 1) {
			throw new UnsupportedOperationException("not yet implemented");
		}
		if (level == 1) {
			return this.variables.size();
		}
		return 0;
	}
}
