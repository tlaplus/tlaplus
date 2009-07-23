package org.lamport.tla.toolbox.util;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.Platform;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.tool.ToolboxLifecycleException;
import org.lamport.tla.toolbox.tool.ToolboxLifecycleParticipant;

/**
 * Provides methods for accessing the extensions registered to the toolbox extension points
 *  
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ToolboxLifecycleParticipantManger
{
    private static final String POINT = "org.lamport.tla.toolbox.participant";
    private static final String CLASS_ATTR_NAME = "class";

    /**
     * Retrieves tools registered
     * @return
     */
    public static ToolboxLifecycleParticipant[] getRegisteredTools() throws ToolboxLifecycleException
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
                throw new ToolboxLifecycleException("Error retrieving the registered tools", e);
            }
        }
        return extensions;
    }

    /**
     * Distributes the initialize message
     * @param participants
     * @throws ToolboxLifecycleException
     */
    public static void initialize(ToolboxLifecycleParticipant[] participants) throws ToolboxLifecycleException
    {
        Assert.isNotNull(participants);
        // Activator.logDebug("Initializing the tools");
        for (int i = 0; i < participants.length; i++)
        {
            participants[i].initialize();
        }
    }

    /**
     * Distributes the terminate message  
     * @param participants
     * @throws ToolboxLifecycleException
     */
    public static void terminate(ToolboxLifecycleParticipant[] participants) throws ToolboxLifecycleException
    {
        Assert.isNotNull(participants);
        // Activator.logDebug("Terminating the tools");
        for (int i = 0; i < participants.length; i++)
        {
            participants[i].terminate();
        }
    }

}
