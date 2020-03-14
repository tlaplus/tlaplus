package org.lamport.tla.toolbox;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.Platform;
import org.lamport.tla.toolbox.lifecycle.ToolboxLifecycleParticipant;

/**
 * Provides methods for accessing the extensions registered to the toolbox extension points
 *  
 * @author Simon Zambrovski
 */
public class ToolboxLifecycleParticipantManger
{
    private static final String POINT = "org.lamport.tla.toolbox.tool";
    private static final String CLASS_ATTR_NAME = "class";

    /**
     * Retrieves tools registered
     * @return
     */
    private static ToolboxLifecycleParticipant[] getRegisteredTools()
    {
        IConfigurationElement[] decls = Platform.getExtensionRegistry().getConfigurationElementsFor(POINT);
        ToolboxLifecycleParticipant[] extensions = new ToolboxLifecycleParticipant[decls.length];

        for (int i = 0; i < decls.length; i++)
        {
            try
            {
                extensions[i] = (ToolboxLifecycleParticipant) decls[i].createExecutableExtension(CLASS_ATTR_NAME);
            } catch (CoreException e)
            {
            	StandaloneActivator.getDefault().logError(e.getMessage(), e);
            	return new ToolboxLifecycleParticipant[0];
            }
        }
        return extensions;
    }

    /**
     * Distributes the initialize message
     * @param participants
     */
    public static void initialize()
    {
    	final ToolboxLifecycleParticipant[] participants = getRegisteredTools();
        Assert.isNotNull(participants);
        // Activator.getDefault().logDebug("Initializing the tools");
        for (int i = 0; i < participants.length; i++)
        {
            participants[i].initialize();
        }
    }

    public static void postWorkbenchWindowOpen() {
		final ToolboxLifecycleParticipant[] participants = getRegisteredTools();
		Assert.isNotNull(participants);
		for (int i = 0; i < participants.length; i++) {
			participants[i].postWorkbenchWindowOpen();
		}
    }
    	
    /**
     * Distributes the terminate message  
     * @param participants
     */
    public static void terminate()
    {
    	final ToolboxLifecycleParticipant[] participants = getRegisteredTools();
        Assert.isNotNull(participants);
        // Activator.getDefault().logDebug("Terminating the tools");
        for (int i = 0; i < participants.length; i++)
        {
            participants[i].terminate();
        }
	}
}
