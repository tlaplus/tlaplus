package org.lamport.tla.toolbox.util;

import org.eclipse.core.resources.IResource;

/**
 * Holds information for marker creation
 * Helper class to ease the methods
 * @author Simon Zambrovski
 * @version $Id$
 */
public class MarkerInformationHolder
{
    final IResource resource;
    final String moduleName;
    final int severityError;
    final int[] coordinates;
    final String message; 
    final String type = TLAMarkerHelper.TOOLBOX_MARKERS_TLAPARSER_MARKER_ID;
    /**
     * @param resource resource to install marker on
     * @param moduleName name of the module
     * @param severityError severity of the error
     * @param coordinates coordinates in the file
     * @param message string message
     * @param type MarkerType (as defined in plugin.xml)
     */
    public MarkerInformationHolder(IResource resource, String moduleName, int severityError, int[] coordinates,
            String message)
    {
        this.resource = resource;
        this.moduleName = moduleName;
        this.severityError = severityError;
        this.coordinates = coordinates;
        this.message = message;
    }
}