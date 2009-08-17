package org.lamport.tla.toolbox.tool.tlc.result;

import org.eclipse.debug.core.ILaunchConfiguration;

/**
 * Interface for the TLC job result presenter used in the extension point 
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface IResultPresenter
{
    
    public String EXTENSION_ID = "org.lamport.tla.toolbox.tlc.processResultPresenter";

    /**
     * Show the results of the launch 
     */
    public void showResults(ILaunchConfiguration configuration);
}
