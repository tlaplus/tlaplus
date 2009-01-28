package org.lamport.tla.toolbox.ui.view;

import org.eclipse.ui.views.markers.MarkerSupportView;

/**
 * This is a standard Eclipse-based problem view, that is able to represent TLA+ Problem markers 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ProblemMarkerView extends MarkerSupportView
{
    
    public final static String ID = "toolbox.view.ProblemMarkerView";
    public final static String CONTENT_GENERATOR_ID = "toolbox.markers.contentGenerator"; 
    
    public ProblemMarkerView()
    {
        super(CONTENT_GENERATOR_ID);
    }

}
