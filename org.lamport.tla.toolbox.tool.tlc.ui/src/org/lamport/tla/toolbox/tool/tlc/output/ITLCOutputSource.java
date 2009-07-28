package org.lamport.tla.toolbox.tool.tlc.output;

/**
 * Represents source of TLC output
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface ITLCOutputSource
{
    /**
     * Adds a listener
     * @param listener
     */
    public void addTLCStatusListener(ITLCOutputListener listener);
    
    /**
     * Removes a listener
     * @param listener
     */
    public void removeTLCStatusListener(ITLCOutputListener listener);

}
