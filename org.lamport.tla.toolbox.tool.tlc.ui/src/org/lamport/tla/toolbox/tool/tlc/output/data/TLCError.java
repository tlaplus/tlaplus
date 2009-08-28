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
    private LinkedList states;
    private TLCError cause;
    private LinkedList actions;
    private int errorCode;

    public TLCError()
    {

    }

    public TLCError(String message)
    {
        this.message = message;
    }

    public void addState(TLCState state)
    {
        if (states == null)
        {
            states = new LinkedList();
        }

        states.add(state);
    }

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

    public final List getStates()
    {
        return states;
    }

    public final LinkedList getActions()
    {
        return actions;
    }

    public final void setActions(LinkedList actions)
    {
        this.actions = actions;
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

    public boolean hasActions()
    {
        return this.actions != null && !this.actions.isEmpty();
    }

    public boolean hasTrace()
    {
        return this.states != null && !this.states.isEmpty();
    }

}
