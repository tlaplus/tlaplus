package org.lamport.tla.toolbox.tool;

/**
 * Describes a basic interface for the tool contribution
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class ToolboxLifecycleParticipant
{
    /**
     * Is called during toolbox initialization
     * The implementation is empty, subclasses may override
     * @throws ToolboxLifecycleException
     */
    public void initialize() throws ToolboxLifecycleException 
    {
        
    }
    
    /**
     * Is called during termination of the toolbox. 
     * The implementation is empty, subclasses may override
     * 
     * @throws ToolboxLifecycleException
     */
    public void terminate() throws ToolboxLifecycleException 
    {
        
    }
}
