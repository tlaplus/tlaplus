package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.LinkedList;
import java.util.List;

/**
 * Representation of the TLC error
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCError
{
    private String message = "";
    private List<TLCState> states;
    private TLCError cause;
    private int errorCode;

    public TLCError()
    {

    }

    /**
     * Add a state to a trace
     * @param state state to add
     */
    public void addState(TLCState state)
    {
        if (states == null)
        {
            states = new LinkedList<TLCState>();
        }

        states.add(state);
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

    public final List<TLCState> getStates()
    {
        return states;
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
    
}
