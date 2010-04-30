package org.lamport.tla.toolbox.tool.prover.util;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

/**
 * Helper methods for the launching of the prover.
 * 
 * @author Daniel Ricketts
 *
 */
public class ProverHelper
{

    /**
     * ID of the marker that contains a boolean attribute indicating if the prover is running
     * on a module.
     */
    public static final String PROVER_RUNNING_MARKER = "org.lamport.tla.toolbox.tool.prover.proverRunning";
    /**
     * ID for the boolean attribute for the {@link ProverHelper#PROVER_RUNNING_MARKER} indicating if the
     * prover is running on a module.
     */
    public static final String PROVER_IS_RUNNING_ATR = "org.lamport.tla.toolbox.tool.prover.isProverRunning";

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

}
