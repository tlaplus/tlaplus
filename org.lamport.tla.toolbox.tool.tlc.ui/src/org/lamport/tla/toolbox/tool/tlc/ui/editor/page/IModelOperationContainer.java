package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

/**
 * Interface for basic model operations
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface IModelOperationContainer
{

    /**
     * Command for running the model checking 
     * @param mode
     */
    public void doRun();
    
    /**
     * Command for running the model checking in debug mode
     */
    // public void doDebug();

    
    /**
     * Command for running the model generation only
     * @param mode
     */
    public void doGenerate();

}