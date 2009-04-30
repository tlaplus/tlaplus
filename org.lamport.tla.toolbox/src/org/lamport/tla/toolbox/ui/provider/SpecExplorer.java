package org.lamport.tla.toolbox.ui.provider;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.ui.navigator.CommonNavigator;
import org.lamport.tla.toolbox.Activator;

/**
 * Specification Explorer
 * @author Simon Zambrovski
 * @version $Id$
 */
public class SpecExplorer extends CommonNavigator
{
    public final static String VIEW_ID = "toolbox.view.SpecView";

    /**
     * Override the method to deliver the root object for the NCE activation
     */
    protected IAdaptable getInitialInput()
    {
        return Activator.getSpecManager();
    }

}
