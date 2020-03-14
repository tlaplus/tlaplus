package org.lamport.tla.toolbox.tool.tlc.result;

import org.lamport.tla.toolbox.tool.tlc.model.Model;

/**
 * Interface for the TLC job result presenter used in the extension point 
 * @author Simon Zambrovski
 */
public interface IResultPresenter
{
    
    public String EXTENSION_ID = "org.lamport.tla.toolbox.tlc.processResultPresenter";

    /**
     * Show the results of the launch 
     */
    public void showResults(Model model);
}
