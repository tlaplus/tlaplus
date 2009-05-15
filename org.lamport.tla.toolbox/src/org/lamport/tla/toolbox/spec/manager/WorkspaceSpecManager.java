package org.lamport.tla.toolbox.spec.manager;

import java.util.Collection;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Iterator;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.nature.TLANature;
import org.lamport.tla.toolbox.ui.handler.CloseSpecHandler;
import org.lamport.tla.toolbox.ui.handler.OpenSpecHandler;
import org.lamport.tla.toolbox.ui.property.GenericSelectionProvider;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/**
 * Specification manager based on the Workspace
 * @version $Id$
 * @author Simon Zambrovski
 */
public class WorkspaceSpecManager extends GenericSelectionProvider implements ISpecManager, IResourceChangeListener,
        IAdaptable
{
    private Hashtable specStorage = new Hashtable(47);
    private Spec loadedSpec = null;

    /**
     * Constructor
     */
    public WorkspaceSpecManager()
    {

        IWorkspace ws = ResourcesPlugin.getWorkspace();

        String specLoadedName = PreferenceStoreHelper.getInstancePreferenceStore().getString(
                IPreferenceConstants.I_SPEC_LOADED);

        IProject[] projects = ws.getRoot().getProjects();
        try
        {

            Spec spec = null;
            for (int i = 0; i < projects.length; i++)
            {
                // changed from projects[i].isAccessible()
                if (projects[i].isOpen())
                {
                    if (projects[i].hasNature(TLANature.ID))
                    {
                        spec = new Spec(projects[i]);
                        addSpec(spec);

                        // load the spec if found
                        if (spec.getName().equals(specLoadedName))
                        {
                            this.setSpecLoaded(spec);
                        }
                    }
                } else
                {
                    // DELETE closed projects
                    projects[i].delete(true, null);
                }
            }
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        ws.addResourceChangeListener(this);
    }

    /**
     * Destructor
     */
    public void terminate()
    {
        IWorkspace ws = ResourcesPlugin.getWorkspace();
        ws.removeResourceChangeListener(this);
        if (this.loadedSpec != null
                && PreferenceStoreHelper.getInstancePreferenceStore().getBoolean(
                        IPreferenceConstants.I_RESTORE_LAST_SPEC))
        {
            PreferenceStoreHelper.getInstancePreferenceStore().setValue(IPreferenceConstants.I_SPEC_LOADED,
                    this.loadedSpec.getName());
        } else
        {
            PreferenceStoreHelper.getInstancePreferenceStore().setValue(IPreferenceConstants.I_SPEC_LOADED, "");
        }

    }

    /*
     * (non-Javadoc)
     * @see org.lamport.tla.toolbox.spec.manager.ISpecManager#addSpec(toolbox.spec.Spec)
     */
    public void addSpec(Spec spec)
    {
        specStorage.put(spec.getName(), spec);
    }

    /*
     * (non-Javadoc)
     * @see org.lamport.tla.toolbox.spec.manager.ISpecManager#getLoadedSpec()
     */
    public Spec getSpecLoaded()
    {
        return this.loadedSpec;
    }

    /*
     * (non-Javadoc)
     * @see org.lamport.tla.toolbox.spec.manager.ISpecManager#getRecentlyOpened()
     */
    public Spec[] getRecentlyOpened()
    {
        Collection specs = specStorage.values();
        return (Spec[]) specs.toArray(new Spec[specs.size()]);
    }

    /*
     * (non-Javadoc)
     * @see org.lamport.tla.toolbox.spec.manager.ISpecManager#getSpecByName(java.lang.String)
     */
    public Spec getSpecByName(String specName)
    {
        return (Spec) specStorage.get(specName);
    }

    /*
     * (non-Javadoc)
     * @see org.lamport.tla.toolbox.spec.manager.ISpecManager#getSpecByRootModule(java.lang.String)
     */
    public Spec getSpecByRootModule(String rootModulePath)
    {
        if (rootModulePath != null)
        {
            Iterator specI = specStorage.values().iterator();
            if (specI.hasNext())
            {
                Spec spec = (Spec) specI.next();
                if (spec.getRootFilename().equals(rootModulePath))
                {
                    return spec;
                }
            }
        }
        return null;
    }

    /*
     * (non-Javadoc)
     * @see org.lamport.tla.toolbox.spec.manager.ISpecManager#setSpecLoaded(toolbox.spec.Spec)
     */
    public void setSpecLoaded(Spec loadedSpec)
    {
        this.loadedSpec = loadedSpec;
        if (this.loadedSpec != null)
        {
            // touch the spec
            this.loadedSpec.setLastModified();
        }
    }

    /*
     * (non-Javadoc)
     * @see
     * org.eclipse.core.resources.IResourceChangeListener#resourceChanged(org.eclipse.core.resources.IResourceChangeEvent
     * )
     */
    public void resourceChanged(IResourceChangeEvent event)
    {
        /*
         * remove elements from the storage if the projects are deleted
         */
        IResource resource = event.getResource();
        if (resource != null && IResource.PROJECT == resource.getType()
                && IResourceChangeEvent.PRE_DELETE == event.getType())
        {
            specStorage.remove(resource.getName());
        }

    }

    /**
     * Renames a spec 
     * @param spec
     * @param newName
     */
    public void renameSpec(Spec spec, String newName)
    {
        boolean setBack = false;
        if (this.loadedSpec == spec)
        {
            // renaming current spec...
            // close it here
            UIHelper.runCommand(CloseSpecHandler.COMMAND_ID, new HashMap());
            setBack = true;
        }
        specStorage.remove(spec.getName());

        IProject project = ResourceHelper.projectRename(spec.getProject(), newName);
        if (project != null)
        {
            spec = new Spec(project);
            addSpec(spec);
        }

        // set the spec
        if (setBack)
        {
            // reopen the spec
            HashMap parameters = new HashMap();
            parameters.put(OpenSpecHandler.PARAM_SPEC, newName);
            UIHelper.runCommand(OpenSpecHandler.COMMAND_ID, parameters);
        } else
        {
            spec.setLastModified();
        }
    }

    /**
     * Removes the specification
     * @param spec specification to remove
     */
    public void removeSpec(Spec spec)
    {
        if (this.loadedSpec == spec)
        {
            // deleting current spec...
            // close it here
            UIHelper.runCommand(CloseSpecHandler.COMMAND_ID, new HashMap());
        }
        ResourceHelper.deleteProject(spec.getProject());
        specStorage.remove(spec.getName());
    }

    /**
     * Constructs a specification name from the proposition string
     * @param proposition a string with spec name 
     * @param firstRun a flag for the first run
     * @return the name of a spec that is not already used.
     */
    public String constructSpecName(String proposition, boolean firstRun)
    {
        Spec existingSpec = getSpecByName(proposition);
        if (existingSpec != null)
        {
            if (firstRun)
            {
                return constructSpecName(proposition.concat("_1"), false);
            } else
            {
                String oldNumber = proposition.substring(proposition.lastIndexOf("_"));
                int number = Integer.parseInt(oldNumber) + 1;
                proposition = proposition.substring(0, proposition.lastIndexOf("_"));
                return constructSpecName(proposition + number, false);
            }
        }

        return proposition;
    }

    /**
     * Retrieves loaded spec encapsulated in to a selection object  
     */
    public ISelection getSelection()
    {
        if (this.loadedSpec != null)
        {
            return new StructuredSelection(this.loadedSpec);
        } else
        {
            return null;
        }
    }

    /**
     * Sets the spec loaded 
     */
    public void setSelection(ISelection selection)
    {
        if (selection == null)
        {
            setSpecLoaded(null);
            return;
        }
        if (selection instanceof IStructuredSelection)
        {
            IStructuredSelection sSelection = (IStructuredSelection) selection;
            if (sSelection.toArray() instanceof Spec[])
            {
                Spec[] specs = (Spec[]) sSelection.toArray();
                if (specs.length == 0)
                {
                    setSpecLoaded(null);
                } else if (specs.length == 1)
                {
                    setSpecLoaded(specs[0]);
                } else
                {
                    throw new IllegalArgumentException("Only one specification can be selected");
                }
            } else
            {
                throw new IllegalArgumentException(
                        "Workspace specification manager only accepts specification objects to be selected");
            }
        } else
        {
            throw new IllegalArgumentException(
                    "Workspace specification manager only accepts specification object in a StructuredSelection");
        }
    }

    /**
     * Only support the interface, no real adaptivity
     */
    public Object getAdapter(Class adapter)
    {
        return null;
    }
}
