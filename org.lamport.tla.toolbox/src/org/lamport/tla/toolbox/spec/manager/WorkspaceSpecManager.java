package org.lamport.tla.toolbox.spec.manager;

import java.util.Collection;
import java.util.Hashtable;
import java.util.Iterator;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.nature.TLANature;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/**
 * Specification manager based on the Workspace
 * @version $Id$
 * @author Simon Zambrovski
 */
public class WorkspaceSpecManager extends AbstractSpecManager implements IResourceChangeListener
{
    private Hashtable storage = new Hashtable(47);
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
        if (this.loadedSpec != null && PreferenceStoreHelper.getInstancePreferenceStore().getBoolean(
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
        storage.put(spec.getName(), spec);
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
        Collection specs = storage.values();
        return (Spec[]) specs.toArray(new Spec[specs.size()]);
    }

    /*
     * (non-Javadoc)
     * @see org.lamport.tla.toolbox.spec.manager.ISpecManager#getSpecByName(java.lang.String)
     */
    public Spec getSpecByName(String specName)
    {
        return (Spec) storage.get(specName);
    }

    /*
     * (non-Javadoc)
     * @see org.lamport.tla.toolbox.spec.manager.ISpecManager#getSpecByRootModule(java.lang.String)
     */
    public Spec getSpecByRootModule(String rootModulePath)
    {
        if (rootModulePath != null)
        {
            Iterator specI = storage.values().iterator();
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
            storage.remove(resource.getName());
        }

    }

}
