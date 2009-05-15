package org.lamport.tla.toolbox.tool.tlc.launch.ui;

import java.util.Vector;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;

/**
 * Provides information about TLC models (launch configurations)
 * in the current project
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelContentProvider implements ITreeContentProvider
{
    private Object[] EMPTY_ARRAY = new Object[0];

    public Object[] getChildren(Object parentElement)
    {
        if (parentElement instanceof ILaunchConfigurationType)
        {
            Spec currentSpec = ToolboxHandle.getCurrentSpec();
            if (currentSpec != null)
            {
                ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
                ILaunchConfigurationType launchConfigurationType = (ILaunchConfigurationType) parentElement;

                Vector modelContributions = new Vector();

                IProject specProject = ToolboxHandle.getCurrentSpec().getProject();
                try
                {
                    ILaunchConfiguration[] launchConfigurations = launchManager
                            .getLaunchConfigurations(launchConfigurationType);
                    for (int i = 0; i < launchConfigurations.length; i++)
                    {
                        // skip launches from other specs (projects)
                        if (!specProject.equals(launchConfigurations[i].getFile().getProject()))
                        {
                            continue;
                        }
                        modelContributions.add(launchConfigurations[i]);
                    }
                } catch (CoreException e)
                {
                    // TODO
                    e.printStackTrace();
                }

                return modelContributions.toArray(new ILaunchConfiguration[modelContributions.size()]);
            }
            return EMPTY_ARRAY;
        } else if (parentElement instanceof ILaunchConfiguration)
        {
            return EMPTY_ARRAY;
        } else
        {
            return EMPTY_ARRAY;
        }

    }

    public Object getParent(Object element)
    {
        if (element instanceof ILaunchConfigurationType)
        {
            return null;
        } else if (element instanceof ILaunchConfiguration)
        {
            try
            {
                if (((ILaunchConfiguration) element).exists()) 
                {
                    return ((ILaunchConfiguration) element).getType();
                } 
            } catch (CoreException e)
            {
                // TODO
                e.printStackTrace();
            }
        }
        return null;
    }

    public boolean hasChildren(Object element)
    {
        return element instanceof ILaunchConfigurationType;
    }

    public Object[] getElements(Object inputElement)
    {
        return getChildren(inputElement);
    }

    public void dispose()
    {
    }

    public void inputChanged(Viewer viewer, Object oldInput, Object newInput)
    {
        // npothing to to do
    }

}
