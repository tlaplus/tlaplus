package org.lamport.tla.toolbox.spec.parser;



/**
 * A parser registry is responsible for distribution of events about changed paer result
 * @author zambrovski
 */
public interface IParserRegistry
{
    /**
     * Adds a listener to be notified on parse result change
     * @param listener a listener instance
     */
    public void addParseResultListener(IParseResultListner listener);
    /**
     * Removes a listener from the list
     * @param listener a listener instance
     */
    public void removeParseResultListener(IParseResultListner listener);
    /**
     * Notification method, that populates the change to the listeners
     * @param result the status new
     */
    public void parseResultChanged(int result);
}
