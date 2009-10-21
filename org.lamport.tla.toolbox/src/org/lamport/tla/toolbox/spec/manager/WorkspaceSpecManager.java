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
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.ui.handlers.IHandlerActivation;
import org.eclipse.ui.handlers.IHandlerService;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.nature.TLANature;
import org.lamport.tla.toolbox.tool.SpecEvent;
import org.lamport.tla.toolbox.ui.handler.CloseSpecHandler;
import org.lamport.tla.toolbox.ui.handler.OpenParseErrorViewHandler;
import org.lamport.tla.toolbox.ui.handler.OpenSpecHandler;
import org.lamport.tla.toolbox.ui.property.GenericSelectionProvider;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.SpecLifecycleManager;
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
    private SpecLifecycleManager lifecycleManager = null;
    private IHandlerActivation parseErrorsHandlerActivation = null;

    /**
     * Constructor
     */
    public WorkspaceSpecManager()
    {
        // initialize the spec life cycle manager
        lifecycleManager = new SpecLifecycleManager();
        lifecycleManager.initialize();

        IProgressMonitor monitor = null;

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
                    projects[i].delete(IResource.FORCE | IResource.ALWAYS_DELETE_PROJECT_CONTENT, monitor);
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
            Activator.logError("Error initializing specification workspace", e);
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
    public void setSpecLoaded(Spec spec)
    {
        if (spec == null)
        {
            // close a spec
            this.lifecycleManager.sendEvent(new SpecEvent(this.loadedSpec, SpecEvent.TYPE_CLOSE));
        } else
        {
            // open a spec
            this.lifecycleManager.sendEvent(new SpecEvent(spec, SpecEvent.TYPE_OPEN));
        }

        this.loadedSpec = spec;
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
        this.lifecycleManager.sendEvent(new SpecEvent(spec, SpecEvent.TYPE_RENAME));
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
        this.lifecycleManager.sendEvent(new SpecEvent(spec, SpecEvent.TYPE_DELETE));
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
     * Is triggered when a spec has been parsed
     * not intended to be called by clients
     */
    public void specParsed(Spec spec)
    {
        /*
         * This controls graying and activating of the menu
         * item Parse Errors which raises the parse errors
         * view. It activates a handler programmatically
         * when appropriate because declaring the handler as a
         * plug in extension did not activate the handler quickly
         * enough. For example, when a parse error is introduced,
         * the Parse Errors menu item would not be active until
         * the user did something such as highlight text. However,
         * by activating it programmatically here, the menu item
         * will become active as soon as there is a parse error
         * and will become inactive as soon as there is no parse
         * error.
         */
        IHandlerService handlerService = (IHandlerService) Activator.getDefault().getWorkbench().getService(
                IHandlerService.class);
        if (parseErrorsHandlerActivation != null)
        {
            /*
             *  It is necessary to deactivate the currently active handler if there
             *  was one because a command can have at most one
             *  active handler at a time.
             * It seems unnecessary to deactivate and reactivate a handler
             * when the parse status goes from error to error, but I cannot
             * find a way to determine if there is currently
             * an active handler for the parse error view command, so the
             * currently active handler is always deactivated, and then reactivated
             * if there is still an error.
             */
            handlerService.deactivateHandler(parseErrorsHandlerActivation);
            parseErrorsHandlerActivation = null;
        }
        if (AdapterFactory.isProblemStatus(spec.getStatus()))
        {
            parseErrorsHandlerActivation = handlerService.activateHandler("toolbox.command.openParseErrorView",
                    new OpenParseErrorViewHandler());
        }

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
    public Object getAdapter(Class adapter)
    {
        return null;
    }

}
