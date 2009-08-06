package org.lamport.tla.toolbox.tool;

import java.util.Vector;

import org.lamport.tla.toolbox.util.TLAMarkerInformationHolder;

/**
 * Representation of the parse result for the tools
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface IParseResult
{
    /**
     * Retrieves the parse status
     * @return
     */
    public int getStatus();
    
    /**
     * Retrieves the list of {@link TLAMarkerInformationHolder} or an empty list
     */
    public Vector getDetectedErrors();
}
