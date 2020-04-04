package org.lamport.tla.toolbox.lifecycle;

import org.eclipse.ui.IWorkbenchWindow;

/**
 * Describes a basic interface for the tool contribution
 * 
 * @author Simon Zambrovski
 */
public abstract class ToolboxLifecycleParticipant
{
    /**
     * Is called during toolbox initialization
     * The implementation is empty, subclasses may override
     */
	public void initialize() {
    	// subclasses may override
	}
    
    /**
     * Is called when the {@link IWorkbenchWindow} has been opened.
     */
    public void postWorkbenchWindowOpen() {
    	// subclasses may override
    }
    
    /**
     * Is called during termination of the toolbox. 
     * The implementation is empty, subclasses may override
     */
	public void terminate(){
    	// subclasses may override
	}
}
