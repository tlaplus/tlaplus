package org.lamport.tla.toolbox.tool;

/**
 * Describes a basic interface for the tool contribution
 * 
 * @author zambrovski
 */
public interface IToolboxContribution
{
    /**
     * Is called during tool initialization
     * @throws ToolInitializationException
     */
    public void initialize() throws ToolInitializationException;
    
    /**
     * Is called during termination of the toolbox
     * @throws ToolInitializationException
     */
    public void terminate() throws ToolInitializationException;
}
