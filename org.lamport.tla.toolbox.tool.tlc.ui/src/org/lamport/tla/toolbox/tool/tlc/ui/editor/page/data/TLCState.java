package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data;

import java.util.Arrays;
import java.util.List;
import java.util.Vector;

/**
 * Representation of the TLC state
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCState
{
    private static final String COLON = ":";
    private static final String CR = "\n";
    private static final String STUTTERING = "Stuttering";
    private static final String AND = "/\\";
    private static final String EQ = " = ";

    /**
     * A factory for stuttering states
     */
    public static TLCState STUTTERING_STATE(int number)
    {
        TLCState state = new TLCState(number);
        state.stuttering = true;
        return state;
    }

    public static TLCState parseState(String input)
    {
        int index = input.indexOf(COLON);
        int index2 = input.indexOf(CR, index);
        if (index2 == -1)
        {
            index2 = input.length();
        }

        int number = Integer.parseInt(input.substring(0, index));
        String label = input.substring(index + 1, index2);
        if (label.indexOf(STUTTERING) != -1)
        {
            return STUTTERING_STATE(number);
        } else
        {
            TLCState state = new TLCState(number);
            state.label = label;
            state.variablesAsString = input.substring(index2 + 1);
            state.variables = TLCState.parseVariables(state.variablesAsString);
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
        String[] stateVarString = null;

        for (int j = 0; j < lines.length; j++)
        {
            index = lines[j].indexOf(AND);
            if (index != -1)
            {
                if (stateVarString != null)
                {
                    TLCVariable var = new TLCVariable(stateVarString[0], TLCVariableValue
                            .parseValue(stateVarString[1]));
                    vars.add(var);
                }

                stateVarString = lines[j].substring(index + AND.length()).split(EQ);
            } else
            {
                stateVarString[1] += CR;
                stateVarString[1] += lines[j];
            }
        }

        // write the last one
        if (stateVarString != null)
        {
            TLCVariable var = new TLCVariable(stateVarString[0], TLCVariableValue
                    .parseValue(stateVarString[1]));
            vars.add(var);
        }

        return (TLCVariable[]) vars.toArray(new TLCVariable[vars.size()]);
    }

    private int number;
    private boolean stuttering = false;
    private String label;
    private String variablesAsString;
    private TLCVariable[] variables = new TLCVariable[0];

    public TLCState(int number)
    {
        this.number = number;
    }

    public boolean isStuttering()
    {
        return stuttering;
    }

    public int getStateNumber()
    {
        return number;
    }

    public final String getLabel()
    {
        return label;
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
}
