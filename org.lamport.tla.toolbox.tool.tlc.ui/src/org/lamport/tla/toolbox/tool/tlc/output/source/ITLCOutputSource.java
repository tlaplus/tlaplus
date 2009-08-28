package org.lamport.tla.toolbox.tool.tlc.output.source;

import org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener;

/**
 * Represents source of TLC output
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface ITLCOutputSource
{
    public final static int PRIO_LOW = 1;
    public final static int PRIO_MEDIUM = 2;
    public final static int PRIO_HIGH = 4;

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

    /**
     * Retrieves the listeners registered by this source
     */
    public ITLCOutputListener[] getListeners();

    /**
     * Retrieves the source name
     */
    public String getSourceName();

    /**
     * Retrieves the source priority
     */
    public int getSourcePrio();

}
