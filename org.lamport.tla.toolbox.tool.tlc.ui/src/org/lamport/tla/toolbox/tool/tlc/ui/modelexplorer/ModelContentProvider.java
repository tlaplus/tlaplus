package org.lamport.tla.toolbox.tool.tlc.ui.modelexplorer;

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
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

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
        if (parentElement instanceof Spec && ToolboxHandle.getCurrentSpec() == parentElement)
        {
            Spec currentSpec = (Spec)parentElement;
            if (currentSpec != null)
            {
                ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
                
                ILaunchConfigurationType configType = launchManager.getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_CONFIGURATION_TYPE);

                Vector models = new Vector();

                IProject specProject = currentSpec.getProject();
                try
                {
                    ILaunchConfiguration[] configs = launchManager.getLaunchConfigurations(configType);
                    for (int i = 0; i < configs.length; i++)
                    {
                        // skip launches from other specs (projects)
                        if (!specProject.equals(configs[i].getFile().getProject()) || !configs[i].exists())
                        {
                            continue;
                        }
                        models.add(configs[i]);
                    }
                } catch (CoreException e)
                {
                    TLCUIActivator.logError("Error fetching the models", e);
                }

                return models.toArray(new ILaunchConfiguration[models.size()]);
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
                TLCUIActivator.logError("Error finding the spec for the model", e);
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
        // nothing to do
    }

}
