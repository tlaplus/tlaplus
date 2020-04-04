package org.lamport.tla.toolbox.tool.tlc.output.source;

import org.lamport.tla.toolbox.tool.tlc.model.Model;
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
    public void addTLCOutputListener(ITLCOutputListener listener);

    /**
     * Removes a listener
     * @param listener
     */
    public void removeTLCOutputListener(ITLCOutputListener listener);

    /**
     * Retrieves the listeners registered by this source
     */
    public ITLCOutputListener[] getListeners();

    /**
     * Retrieves the source name, which is the id of the source
     */
    public Model getModel();

    /**
     * Retrieves the source priority
     * one of the {@link ITLCOutputSource#PRIO_LOW}, {@link ITLCOutputSource#PRIO_MEDIUM}, {@link ITLCOutputSource#PRIO_HIGH}
     */
    public int getSourcePrio();

}
