package org.lamport.tla.toolbox.tool;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.Platform;

/**
 * Provides methods for accessing the extensions 
 * @author zambrovski
 */
public class ToolboxContributionManger
{
    private static final String POINT = "org.lamport.tla.toolbox.tool";

    public static IToolboxContribution[] getToolobxContributions()
    {
        IConfigurationElement[] decls = Platform.getExtensionRegistry().getConfigurationElementsFor(POINT);
        IToolboxContribution[] extensions = new IToolboxContribution[decls.length];

        for (int i = 0; i < decls.length; i++)
        {
            try
            {
                extensions[i] = (IToolboxContribution) decls[i].createExecutableExtension("classname");
            } catch (CoreException e)
            {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }
        return extensions;
    }

    public static IToolboxContribution getToolobxContribution(String name)
    {
        if (name == null)
        {
            return null;
        }
        IConfigurationElement[] decls = Platform.getExtensionRegistry().getConfigurationElementsFor(POINT);
        for (int i = 0; i < decls.length; i++)
        {
            if (name.equals(decls[i].getAttribute("name")))
            {

                try
                {
                    return (IToolboxContribution) decls[i].createExecutableExtension("classname");
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
