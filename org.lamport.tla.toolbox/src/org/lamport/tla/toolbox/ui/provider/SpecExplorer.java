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

    protected IAdaptable getInitialInput()
    {
        return Activator.getSpecManager();
    }

}
