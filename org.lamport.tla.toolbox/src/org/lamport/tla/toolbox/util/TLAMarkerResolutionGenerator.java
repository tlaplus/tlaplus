package org.lamport.tla.toolbox.util;

import org.eclipse.core.resources.IMarker;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IMarkerResolution;
import org.eclipse.ui.IMarkerResolutionGenerator;
import org.eclipse.ui.views.markers.WorkbenchMarkerResolution;
import org.lamport.tla.toolbox.Activator;

/**
 * Marker resolution generator is a factory of marker resoution (also known as quick fixes)
 * @author zambrovski
 */
public class TLAMarkerResolutionGenerator implements IMarkerResolutionGenerator
{

    public IMarkerResolution[] getResolutions(IMarker marker)
    {
        return new DummyMarkerResolution[]{new DummyMarkerResolution(marker)};
    }

    
    public static class DummyMarkerResolution implements IMarkerResolution
    {

        private IMarker problem;
        
        public DummyMarkerResolution(IMarker problem)
        {
            this.problem = problem;
        }
        
        /* (non-Javadoc)
         * @see org.eclipse.ui.IMarkerResolution#getLabel()
         */
        public String getLabel()
        {
            return "Resolution of the problem " + problem.getAttribute(IMarker.MESSAGE, "");
        }

        /* (non-Javadoc)
         * @see org.eclipse.ui.IMarkerResolution#run(org.eclipse.core.resources.IMarker)
         */
        public void run(IMarker marker)
        {
            Activator.logDebug("Marker on " + marker.getAttribute(IMarker.LOCATION, "") + " quick fixed.");
        }
        
    }
    
    
    public static class DummyWBMarkerResolution extends WorkbenchMarkerResolution 
    {

        /* (non-Javadoc)
         * @see org.eclipse.ui.views.markers.WorkbenchMarkerResolution#findOtherMarkers(org.eclipse.core.resources.IMarker[])
         */
        public IMarker[] findOtherMarkers(IMarker[] markers)
        {
            return null;
        }

        /* (non-Javadoc)
         * @see org.eclipse.ui.IMarkerResolution2#getDescription()
         */
        public String getDescription()
        {
            return null;
        }

        /* (non-Javadoc)
         * @see org.eclipse.ui.IMarkerResolution2#getImage()
         */
        public Image getImage()
        {
            return null;
        }

        /* (non-Javadoc)
         * @see org.eclipse.ui.IMarkerResolution#getLabel()
         */
        public String getLabel()
        {
            return null;
        }

        /* (non-Javadoc)
         * @see org.eclipse.ui.IMarkerResolution#run(org.eclipse.core.resources.IMarker)
         */
        public void run(IMarker marker)
        {
            
        }
        
    }
}
