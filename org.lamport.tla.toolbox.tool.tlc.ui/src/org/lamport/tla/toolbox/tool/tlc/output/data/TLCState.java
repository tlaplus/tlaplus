package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.Arrays;
import java.util.List;
import java.util.Vector;

import org.lamport.tla.toolbox.tool.tlc.ui.util.IModuleLocatable;

import tla2sany.st.Location;

/**
 * Representation of the TLC state
 * @author Simon Zambrovski
 * @version $Id$
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
    private static TLCVariable[] parseVariables(String variablesText)
    {
        String[] lines = variablesText.split(CR);
        Vector vars = new Vector();
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

        return (TLCVariable[]) vars.toArray(new TLCVariable[vars.size()]);
    }

    private int number;
    private boolean stuttering = false;
    private boolean isBackToState = false;
    private String label;
    private String variablesAsString;
    private TLCVariable[] variables = new TLCVariable[0];
    /**
     * Contains the location of the action
     * which caused this state
     */
    private Location location;
    /**
     * The name of the model for which this
     * is a state.
     */
    private String modelName;

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

    public final List getVariablesAsList()
    {
        return Arrays.asList(variables);
    }

    public final TLCVariable[] getVariables()
    {
        return variables;
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
        for (int i = 0; i < variables.length; i++)
        {
            TLCVariable var = variables[i];
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
}
