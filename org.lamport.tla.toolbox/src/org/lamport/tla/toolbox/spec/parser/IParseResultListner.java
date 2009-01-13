package org.lamport.tla.toolbox.spec.parser;


/**
 * A listener of the parse result
 * @author zambrovski
 */
public interface IParseResultListner
{
    /**
     * Inform the listener about the status change
     * @param parseStatus a value from {@link IParseConstants}
     */
    public void parseResultChanged(int parseStatus);
}
