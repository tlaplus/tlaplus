package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data;

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
        
        int number = Integer.parseInt(input.substring(0, index ));
        String label = input.substring(index, index2);
        if (label.indexOf(STUTTERING) != -1) 
        {
            return STUTTERING_STATE(number);
        } else {
            TLCState state = new TLCState(number);
            state.label = label;
            state.variables = input.substring(index2 + 1);
            return state;
        }
    }

    
    private String label;
    private String variables;
    private int number;
    private boolean stuttering = false;
    
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
    
    public final String getVariables()
    {
        return variables;
    }
}
