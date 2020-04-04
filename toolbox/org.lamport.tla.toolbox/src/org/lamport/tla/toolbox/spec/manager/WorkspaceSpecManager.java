package org.lamport.tla.toolbox.spec.manager;

import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
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
import org.eclipse.core.runtime.IAdapterFactory;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.nature.TLANature;
import org.lamport.tla.toolbox.tool.SpecEvent;
import org.lamport.tla.toolbox.tool.SpecLifecycleParticipant;
import org.lamport.tla.toolbox.tool.SpecRenameEvent;
import org.lamport.tla.toolbox.ui.property.GenericSelectionProvider;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.SpecLifecycleManager;
import org.lamport.tla.toolbox.util.compare.SpecComparator;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/**
 * Specification manager based on the Workspace
 * @version $Id$
 * @author Simon Zambrovski
 */
public class WorkspaceSpecManager extends GenericSelectionProvider implements ISpecManager, IResourceChangeListener,
        IAdaptable, IAdapterFactory
{
    private Hashtable<String, Spec> specStorage = new Hashtable<String, Spec>(47);
    private Spec loadedSpec = null;
    private SpecLifecycleManager lifecycleManager = null;

    /**
     * Constructor
     */
    public WorkspaceSpecManager(final IProgressMonitor monitor)
    {
        // initialize the spec life cycle manager
        lifecycleManager = new SpecLifecycleManager();

        final IWorkspace ws = ResourcesPlugin.getWorkspace();

        final String specLoadedName = PreferenceStoreHelper.getInstancePreferenceStore().getString(
                IPreferenceConstants.I_SPEC_LOADED);

        final IProject[] projects = ws.getRoot().getProjects();
        try
        {

            for (int i = 0; i < projects.length; i++)
            {
                // changed from projects[i].isAccessible()
                final IProject project = projects[i];
				if (project.isOpen())
                {
                    if (project.hasNature(TLANature.ID))
                    {
						// Refresh the project in case the actual on-disk
						// representation and the cached Eclipse representation
						// have diverged. This can happen when e.g. another
						// Toolbox opens the project or the files get manually
						// edited. Without calling refresh, code down below 
                    	// might throw exceptions due to out-of-sync problems.  
                    	project.refreshLocal(IResource.DEPTH_INFINITE, monitor);
                        
                    	final Spec spec = new Spec(project);
                        // Added by LL on 12 Apr 2011
                        // If spec.rootFile = null, then this is a bad spec. So
                        // we should report it and not perform addSpec(spec).  It
                        // would be nice if we could report it to the user, but
                        // it seems to be impossible to popup a window at this point
                        // in the code.
                        if (spec.getRootFile() == null)
                        {
                            Activator.getDefault().logError("The bad spec is: `" + project.getName() + "'", null);
                        } else
                        {
                            // This to threw a null pointer exception for Tom, probably causing the abortion
                            // of the Toolbox start. But it started on the next attempt.  Should we catch the
                            // and perhaps report the bad spec?
                            addSpec(spec);
                        }
                        
                        // load the spec if found
                        if (spec.getName().equals(specLoadedName))
                        {
                            this.setSpecLoaded(spec);
                        }
                    }
                } else
                {
                    // DELETE closed projects
                    project.delete(IResource.FORCE | IResource.ALWAYS_DELETE_PROJECT_CONTENT, monitor);
                }
            }

            if (specLoadedName != null && !specLoadedName.equals("") && this.loadedSpec == null)
            {
                // there was a spec loaded but it was not found
                // explicit un-set it
                setSpecLoaded(null);
            }

        } catch (CoreException e)
        {
            Activator.getDefault().logError("Error initializing specification workspace", e);
        }

        ws.addResourceChangeListener(this);
        
        Platform.getAdapterManager().registerAdapters(this, IProject.class);
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
        lifecycleManager.sendEvent(new SpecEvent(spec, SpecEvent.TYPE_CREATE));
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
        Collection<Spec> specs = specStorage.values();
        return specs.toArray(new Spec[specs.size()]);
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
            Iterator<Spec> specI = specStorage.values().iterator();
            while (specI.hasNext())
            {
                Spec spec = specI.next();
                // try/catch added by LL on 12 April 2011 because
                // corrupted database can cause the call of getRootFileName() to
                // throw a null pointer exception.
                try
                {
                    if (spec.getRootFilename().equals(rootModulePath))
                    {
                        return spec;
                    }
                } catch (Exception e)
                {
                	e.printStackTrace();
                    // Just ignore the exception and pray.
                }
            }
        }
        return null;
    }

    /*
     * (non-Javadoc)
     * @see org.lamport.tla.toolbox.spec.manager.ISpecManager#setSpecLoaded(toolbox.spec.Spec)
     */
    public void setSpecLoaded(Spec spec)
    {
        if (spec == null)
        {
            // close a spec
            // modified by LL on 30 May 2010 to add the follow test that
            // there is a loaded spec to close.
            if (this.loadedSpec != null)
            {
                this.lifecycleManager.sendEvent(new SpecEvent(this.loadedSpec, SpecEvent.TYPE_CLOSE));
            }
        } else
        {
            // open a spec
            this.lifecycleManager.sendEvent(new SpecEvent(spec, SpecEvent.TYPE_OPEN));
        }

        this.loadedSpec = spec;
        if (this.loadedSpec != null)
        {
            // touch the spec, but why? This is essentially going to cause a spec rebuild
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
     * Renames the given spec to the given name 
     * @param spec
     * @param newName
     */
    public void renameSpec(final Spec oldSpec, final String newName, final IProgressMonitor aMonitor)
    {
        // remove from storage
        specStorage.remove(oldSpec.getName());

        // rename the underlying resource
        final IProject project = ResourceHelper.projectRename(oldSpec.getProject(), newName, aMonitor);
        
        // create new project with updated name
        final Spec newSpec = new Spec(project);
        newSpec.setLastModified();

        // add it to storage
        addSpec(newSpec);
        
        this.lifecycleManager.sendEvent(new SpecRenameEvent(oldSpec, newSpec));
        
        try {
			// Renaming a spec constitutes various updates/changes in dependent
			// bundles such as the TLC Model. A Model indirectly references the
        	// old IProject through its ILaunchConfiguration. Thus, defer the
        	// deletion of the old IProject _after_ dependent bundles had a 
        	// chance to react to the renaming event.
			oldSpec.getProject().delete(IResource.NONE, aMonitor);
		} catch (CoreException shouldNotHappen) {
			shouldNotHappen.printStackTrace();
		}
    }
    
    /**
	 * Removes the specification always deleting project content (files).
	 * 
	 * @see #removeSpec(Spec, IProgressMonitor, boolean)
	 * @param spec
	 *            specification to remove
	 * @param aMonitor
	 *            a monitor to track progress
	 */
    public void removeSpec(final Spec spec, final IProgressMonitor aMonitor)
    {
    	removeSpec(spec, aMonitor, true);
    }

    /**
     * Removes the specification.  
     * Modified 3 August 2011 by LL to add the boolean argument to say if this
     * is a Forget command, which doesn't delete the spec's .toolbox directory,
     * or a Delete command, which does.
     * 
     * @param spec specification to remove
     * @param aMonitor a monitor to track progress
     * @param isForget do not delete .toolbox directory
     */
    public void removeSpec(final Spec spec, final IProgressMonitor aMonitor, boolean isForget)
    {
        this.lifecycleManager.sendEvent(new SpecEvent(spec, SpecEvent.TYPE_DELETE));
        ResourceHelper.deleteProject(spec.getProject(), aMonitor, isForget);
        specStorage.remove(spec.getName());
        if (loadedSpec == spec) {
			// If the spec being deleted is the current open one, unset the
			// loadedSpec. Otherwise getMostRecentlyOpenedSpec will return the
			// deleted one later if no other spec is opened in between.
        	loadedSpec = null;
        }
    }

    /**
     * Is triggered when a spec has been parsed
     * not intended to be called by clients
     */
    public void specParsed(Spec spec)
    {
        // inform the participants
        this.lifecycleManager.sendEvent(new SpecEvent(spec, SpecEvent.TYPE_PARSE));
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
    public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter)
    {
        return null;
    }

	public Collection<Spec> getSpecs() {
		return Collections.unmodifiableCollection(specStorage.values());
	}

    /**
     * @return The {@link Spec} most recently opened or null if no specs are known
     */
    public Spec getMostRecentlyOpenedSpec()
    {
        if (loadedSpec != null)
        {
            return loadedSpec;
        }

        final Comparator<Spec> comparator = new SpecComparator();
        
        // no spec currently open
        // search for the last spec to be closed
        Spec[] specs = getRecentlyOpened();
        Spec mostRecentlyOpened = null;
        for (int i = 0; i < specs.length; i++)
        {
        	int compare = comparator.compare(mostRecentlyOpened, specs[i]);
        	if(compare > 0) {
        		mostRecentlyOpened = specs[i];
        	}
        }

        return mostRecentlyOpened;
    }

	/**
	 * @return Whether the given spec is the currently loaded spec
	 */
	public boolean isSpecLoaded(final Spec aSpec) {
		return getSpecLoaded() == aSpec;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.runtime.IAdapterFactory#getAdapter(java.lang.Object, java.lang.Class)
	 */
	public Object getAdapter(final Object adaptableObject,
			@SuppressWarnings("rawtypes") final Class adapterType) {
		if (adaptableObject instanceof IProject) {
			final IProject project = (IProject) adaptableObject;
			final String key = project.getName();
			return specStorage.get(key);
		}
		return null;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.runtime.IAdapterFactory#getAdapterList()
	 */
	@SuppressWarnings("rawtypes")
	public Class[] getAdapterList() {
		return new Class[] { Spec.class };
	}

	public void addSpecLifecycleParticipant(SpecLifecycleParticipant specLifecycleParticipant) {
		this.lifecycleManager.addSpecLifecycleParticipant(specLifecycleParticipant);
	}

	public void removeSpecLifecycleParticipant(SpecLifecycleParticipant specLifecycleParticipant) {
		this.lifecycleManager.removeSpecLifecycleParticipant(specLifecycleParticipant);
	}
}
