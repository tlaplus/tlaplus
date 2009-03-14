package org.lamport.tla.toolbox.tool;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.Platform;

/**
 * Provides methods for accessing the extensions registered to the toolbox extension points
 *  
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ToolboxContributionManger
{
    private static final String POINT = "org.lamport.tla.toolbox.tool";
    private static final String CLASS_ATTR_NAME = "classname";
    private static final String NAME_ATTR_NAME = "name";

    /**
     * Retrieves tools registered
     * @return
     */
    public static IToolboxContribution[] getRegisteredTools()
    {
        IConfigurationElement[] decls = Platform.getExtensionRegistry().getConfigurationElementsFor(POINT);
        IToolboxContribution[] extensions = new IToolboxContribution[decls.length];

        for (int i = 0; i < decls.length; i++)
        {
            try
            {
                extensions[i] = (IToolboxContribution) decls[i].createExecutableExtension(CLASS_ATTR_NAME);
            } catch (CoreException e)
            {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }
        return extensions;
    }

    /**
     * Retrieves the registered extensions using the tool extension point using the name attribute
     * @param name
     * @return the tool with provided name, or null of no match
     */
    public static IToolboxContribution getRegisteredTool(String name)
    {
        if (name == null)
        {
            return null;
        }
        IConfigurationElement[] decls = Platform.getExtensionRegistry().getConfigurationElementsFor(POINT);
        for (int i = 0; i < decls.length; i++)
        {
            if (name.equals(decls[i].getAttribute(NAME_ATTR_NAME)))
            {
                try
                {
                    return (IToolboxContribution) decls[i].createExecutableExtension(CLASS_ATTR_NAME);
                } catch (CoreException e)
                {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
            }
        }

        return null;
    }

}
