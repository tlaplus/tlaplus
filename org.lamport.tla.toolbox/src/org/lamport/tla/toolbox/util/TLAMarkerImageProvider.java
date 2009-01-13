package org.lamport.tla.toolbox.util;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.ui.internal.ide.IMarkerImageProvider;

/**
 * Provider for images in the problems view
 * @author zambrovski
 */
public class TLAMarkerImageProvider implements IMarkerImageProvider {
    /**
     * TaskImageProvider constructor comment.
     */
    public TLAMarkerImageProvider() {
        super();
    }

    /**
     * Returns the relative path for the image
     * to be used for displaying an marker in the workbench.
     * This path is relative to the plugin location
     *
     * Returns <code>null</code> if there is no appropriate image.
     *
     * @param marker The marker to get an image path for.
     * <br>
     * @see org.eclipse.ui.internal.ide.ProblemImageProvider
     */
    public String getImagePath(IMarker marker) {
        String iconPath = "/icons/full/";//$NON-NLS-1$      
        if (isMarkerType(marker, TLAMarkerHelper.TOOLBOX_MARKERS_PROBLEM_MARKER_ID)) {
            switch (marker.getAttribute(IMarker.SEVERITY,
                    IMarker.SEVERITY_WARNING)) {
            case IMarker.SEVERITY_ERROR:
                return iconPath + "obj16/error_tsk.gif";//$NON-NLS-1$
            case IMarker.SEVERITY_WARNING:
                return iconPath + "obj16/warn_tsk.gif";//$NON-NLS-1$
            case IMarker.SEVERITY_INFO:
                return iconPath + "obj16/info_tsk.gif";//$NON-NLS-1$
            }
        }
        return null;
    }

    /**
     * Returns whether the given marker is of the given type (either directly or indirectly).
     */
    private boolean isMarkerType(IMarker marker, String type) {
        try {
            return marker.isSubtypeOf(type);
        } catch (CoreException e) {
            return false;
        }
    }
}
