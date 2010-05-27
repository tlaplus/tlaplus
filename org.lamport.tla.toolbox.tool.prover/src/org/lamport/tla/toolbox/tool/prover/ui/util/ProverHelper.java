package org.lamport.tla.toolbox.tool.prover.ui.util;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.lamport.tla.toolbox.tool.ToolboxHandle;

/**
 * Helper methods for the launching of the prover.
 * 
 * @author Daniel Ricketts
 *
 */
public class ProverHelper
{

    /**
     * Type of the marker that contains a boolean attribute indicating if the prover is running
     * on a module.
     */
    public static final String PROVER_RUNNING_MARKER = "org.lamport.tla.toolbox.tool.prover.proverRunning";
    /**
     * ID for the boolean attribute for the {@link ProverHelper#PROVER_RUNNING_MARKER} indicating if the
     * prover is running on a module.
     */
    public static final String PROVER_IS_RUNNING_ATR = "org.lamport.tla.toolbox.tool.prover.isProverRunning";
    /**
     * Type of a marker that contains information about an obligation. 
     */
    public static final String OBLIGATION_MARKER = "org.lamport.tla.toolbox.tool.prover.obligation";
    /**
     * Attribute on an obligation marker giving the integer id of the obligation.
     */
    public static final String OBLIGATION_ID = "org.lamport.tla.toolbox.tool.prover.obId";
    /**
     * Attribute on an obligation marker giving the String status of the obligation.
     */
    public static final String OBLIGATION_STATUS = "org.lamport.tla.toolbox.tool.prover.obStatus";
    /**
     * Attribute on an obligation marker giving the String method of the obligation.
     */
    public static final String OBLIGATION_METHOD = "org.lamport.tla.toolbox.tool.prover.obMethod";
    /**
     * Attribute on an obligation marker giving the formatted String of the obligation.
     */
    public static final String OBLIGATION_STRING = "org.lamport.tla.toolbox.tool.prover.obString";

    /**
     * Signals using a marker that the prover is or is not running
     * on module.
     * 
     * @param module
     * @param isRunning whether the prover is running or not on module
     * @throws CoreException 
     */
    public static void setProverRunning(IResource module, boolean isRunning) throws CoreException
    {
        if (module.exists())
        {
            IMarker marker;
            // Try to find any existing markers.
            IMarker[] foundMarkers = module.findMarkers(PROVER_RUNNING_MARKER, false, IResource.DEPTH_ZERO);

            // There should only be one such marker at most.
            // In case there is more than one existing marker,
            // remove extra markers.
            if (foundMarkers.length > 0)
            {
                marker = foundMarkers[0];
                // remove trash if any
                for (int i = 1; i < foundMarkers.length; i++)
                {
                    foundMarkers[i].delete();
                }
            } else
            {
                // Create a new marker if no existing ones.
                marker = module.createMarker(PROVER_RUNNING_MARKER);
            }

            // Set the boolean attribute to indicate if the marker is running.
            marker.setAttribute(PROVER_IS_RUNNING_ATR, isRunning);
        }

    }

    /**
     * Returns whether or not the prover is running on the module.
     * 
     * @param module
     * @return
     * @throws CoreException 
     */
    public static boolean isProverRunning(IResource module) throws CoreException
    {
        if (module.exists())
        {
            IMarker marker;
            // Try to find any existing markers.
            IMarker[] foundMarkers = module.findMarkers(PROVER_RUNNING_MARKER, false, IResource.DEPTH_ZERO);

            // There should only be one such marker at most.
            // In case there is more than one existing marker,
            // remove extra markers.
            if (foundMarkers.length > 0)
            {
                marker = foundMarkers[0];
                // remove trash if any
                for (int i = 1; i < foundMarkers.length; i++)
                {
                    foundMarkers[i].delete();
                }

                return marker.getAttribute(PROVER_IS_RUNNING_ATR, false);
            } else
            {
                return false;
            }
        } else
        {
            return false;
        }
    }

    /**
     * Removes all markers indicating obligation information on  a resource. Does
     * nothing if the resource does not exist. It deletes these markers only at one level
     * under the resource.
     * 
     * @param resource
     * @throws CoreException 
     */
    public static void clearObligationMarkers(IResource resource) throws CoreException
    {
        if (resource.exists())
        {
            /*
             * Obligation markers should only be on files directly in the project folder, so we
             * only need to delete markers to depth one. Depth infinite would search any
             * checkpoint folders, which can be slow if there are many files.
             */
            resource.deleteMarkers(OBLIGATION_MARKER, false, IResource.DEPTH_ONE);
        }
    }

    /**
     * Returns true iff the marker is of the type
     * {@link ProverHelper#OBLIGATION_MARKER} and represents
     * an obligation that is in an "interesting" state. Interesting
     * generally means that the obligation has not been proved or
     * checked.
     * 
     * @param marker
     * @return
     * @throws CoreException 
     */
    public static boolean isInterestingObligation(IMarker marker)
    {
        /*
         * Should return true iff that status is one of some collection of strings.
         * 
         * TODO update this method once we know what those strings are.
         */
        String obStatus = marker.getAttribute(OBLIGATION_STATUS, "");
        return obStatus.equals("beingproved") || obStatus.equals("failed")
                || obStatus.equals("failed (already processed");
    }

    /**
     * Returns all {@link IMarker} of type {@link ProverHelper#OBLIGATION_MARKER}
     * for the currently opened spec. These markers contain information about obligations.
     * 
     * If there is no spec currently open in the toolbox, this returns null.
     * 
     * @return
     * @throws CoreException 
     */
    public static IMarker[] getObMarkersCurSpec() throws CoreException
    {

        if (ToolboxHandle.getCurrentSpec() != null)
        {
            return ToolboxHandle.getCurrentSpec().getProject().findMarkers(OBLIGATION_MARKER, false,
                    IResource.DEPTH_ONE);
        }

        return null;

    }

}
