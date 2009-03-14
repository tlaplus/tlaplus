package org.lamport.tla.toolbox.tool;

/**
 * Describes a basic interface for the tool contribution
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface IToolboxContribution
{
    /**
     * Is called during tool initialization
     * @throws ToolLifecycleException
     */
    public void initialize() throws ToolLifecycleException;
    
    /**
     * Is called during termination of the toolbox
     * @throws ToolLifecycleException
     */
    public void terminate() throws ToolLifecycleException;
}
