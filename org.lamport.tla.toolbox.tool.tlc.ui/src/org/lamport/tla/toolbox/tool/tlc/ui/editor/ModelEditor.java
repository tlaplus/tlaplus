package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.custom.CTabFolder2Adapter;
import org.eclipse.swt.custom.CTabFolder2Listener;
import org.eclipse.swt.custom.CTabFolderEvent;
import org.eclipse.swt.custom.CTabItem;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IPartService;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.forms.IMessageManager;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.editor.IFormPage;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.ITextEditor;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.AdvancedModelPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.BasicFormPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.MainModelPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.ResultPage;
import org.lamport.tla.toolbox.tool.tlc.ui.preference.ITLCPreferenceConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.util.ModelEditorPartListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.SemanticHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.view.TLCErrorView;
import org.lamport.tla.toolbox.tool.tlc.util.ChangedSpecModulesGatheringDeltaVisitor;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper.IFileProvider;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.ModuleNode;

/**
 * Editor for the model
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelEditor extends FormEditor implements ModelHelper.IFileProvider
{

    /**
     * Editor ID
     */
    public static final String ID = "org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor";

    /*
     * working copy of the model
     */
    private ILaunchConfigurationWorkingCopy configurationCopy;
    // helper to resolve semantic matches of words
    private SemanticHelper helper;
    // reacts on model changes
    private IResourceChangeListener modelFileChangeListener;

    /**
     * This runnable is responsible for the validation of the pages.
     * It iterates over the pages and calls validate on them. At this point it assumes,
     * that every page is a subclass of the BasicFormPage.
     * This runnable must be called in the UI thread (using UIHelper.runUIAsync() method).
     * It is used in the workspace root listener and is called once after the input is set and after the pages 
     * are added.
     */
    private ValidateRunnable validateRunable = new ValidateRunnable();

    private class ValidateRunnable implements Runnable
    {

        private boolean switchToErrorPage = false;

        public void run()
        {
            // re-validate the pages, iff the model is not running
            // and is not locked
            if (!isModelRunning() && !isModelLocked())
            {
                /*
                 * Note that all pages are not necessarily
                 * instances of BasicFormPage. Some are read
                 * only editors showing saved versions of
                 * modules.
                 */
                for (int i = 0; i < getPageCount(); i++)
                {
                    if (pages.get(i) instanceof BasicFormPage)
                    {
                        BasicFormPage page = (BasicFormPage) pages.get(i);
                        page.resetAllMessages(true);
                    }
                }
                for (int i = 0; i < getPageCount(); i++)
                {
                    if (pages.get(i) instanceof BasicFormPage)
                    {
                        BasicFormPage page = (BasicFormPage) pages.get(i);
                        // re-validate the model on changes of the spec
                        page.validatePage(switchToErrorPage);
                    }
                }
            }
        }
    };

    // react on spec file changes
    private IResourceChangeListener workspaceResourceChangeListener = new IResourceChangeListener() {
        public void resourceChanged(IResourceChangeEvent event)
        {
            IResourceDelta delta = event.getDelta();

            /**
             * This is a helper method that returns a new instance of ChangedModulesGatheringDeltaVisitor,
             * which gathers the changed TLA modules from a resource delta tree.
             */
            ChangedSpecModulesGatheringDeltaVisitor visitor = new ChangedSpecModulesGatheringDeltaVisitor(getConfig()) {
                public IResource getModel()
                {
                    return ModelEditor.this.getConfig().getFile();
                }
            };

            try
            {
                delta.accept(visitor);
                List modules = visitor.getModules();
                // one of the modules in the specification has changed
                // this means that identifiers defined in a spec might have changed
                // re-validate the editor
                if (!modules.isEmpty() || visitor.isModelChanged() || visitor.getCheckpointChanged())
                {
                    // update the specObject of the helper
                    helper.resetSpecNames();

                    // iff the model has changed, switch to the error page after the validation
                    validateRunable.switchToErrorPage = visitor.isModelChanged();

                    // re-validate the pages
                    UIHelper.runUIAsync(validateRunable);

                    return;
                }
            } catch (CoreException e)
            {
                TLCUIActivator.logError("Error visiting changed resource", e);
                return;
            }

        }
    };

    // data binding manager
    private DataBindingManager dataBindingManager = new DataBindingManager();

    /**
     * A listener that reacts to when editor tabs showing saved modules
     * get closed. This listener properly disposes of the editor and its contents.
     * See the class documentation for more details.
     */
    private CTabFolder2Listener listener = new CloseModuleTabListener();

    // array of pages to add
    private BasicFormPage[] pagesToAdd;

    /**
     * Simple editor constructor
     */
    public ModelEditor()
    {
        helper = new SemanticHelper();
        pagesToAdd = new BasicFormPage[] { new MainModelPage(this), new AdvancedModelPage(this), new ResultPage(this) };
    }

    /**
     * Initialize the editor
     */
    public void init(IEditorSite site, IEditorInput input) throws PartInitException
    {
        // TLCUIActivator.logDebug("entering ModelEditor#init(IEditorSite site, IEditorInput input)");
        super.init(site, input);

        // grab the input
        FileEditorInput finput = getFileEditorInput();
        if (finput != null)
        {
            ILaunchConfiguration configuration = ModelHelper.getModelByFile(finput.getFile());

            try
            {
                configurationCopy = configuration.getWorkingCopy();
            } catch (CoreException e)
            {
                TLCUIActivator.logError("Could not load model content for " + finput.getName(), e);
            }

            /*
             * Install a resource change listener on the file opened which react
             * on marker changes
             */
            modelFileChangeListener = ModelHelper.installModelModificationResourceChangeListener(this,
            /*
             * If the model file is changed, refresh the changes in the
             * editor if the model is in use, activate the third page
             */
            new Runnable() {
                public void run()
                {
                    // update the pages
                    for (int i = 0; i < getPageCount(); i++)
                    {
                        /*
                         * Note that all pages are not necessarily
                         * instances of BasicFormPage. Some are read
                         * only editors showing saved versions of
                         * modules.
                         */
                        if (pages.get(i) instanceof BasicFormPage)
                        {
                            BasicFormPage page = (BasicFormPage) pages.get(i);
                            ((BasicFormPage) page).refresh();
                        }
                    }

                    if (isModelRunning())
                    {
                        showResultPage();
                    }
                    // evtl. add more graphical sugar here,
                    // like changing the model icon,
                    // changing the editor title (part name)
                }
            });

            // setContentDescription(path.toString());
            this.setPartName(ModelHelper.getModelName(finput.getFile()));
            this.setTitleToolTip(finput.getFile().getProjectRelativePath().toString());

            // add a listener that will update the tlc error view when a model editor
            // is made visible
            IPartService service = (IPartService) getSite().getService(IPartService.class);
            service.addPartListener(ModelEditorPartListener.getDefault());

        }

        /*
         * Install resource change listener on the workspace root to react on any changes in th current spec
         */
        ResourcesPlugin.getWorkspace().addResourceChangeListener(workspaceResourceChangeListener,
                IResourceChangeEvent.POST_BUILD);

        // update the spec object of the helper
        helper.resetSpecNames();

        // initial re-validate the pages, which are already loaded
        UIHelper.runUIAsync(validateRunable);
        // TLCUIActivator.logDebug("leaving ModelEditor#init(IEditorSite site, IEditorInput input)");

    }

    /**
     * @see org.eclipse.ui.forms.editor.FormEditor#dispose()
     */
    public void dispose()
    {
        // TLCUIActivator.logDebug("entering ModelEditor#dispose()");
        // remove the listeners
        ResourcesPlugin.getWorkspace().removeResourceChangeListener(workspaceResourceChangeListener);
        ResourcesPlugin.getWorkspace().removeResourceChangeListener(modelFileChangeListener);
        super.dispose();
        // TLCUIActivator.logDebug("leaving ModelEditor#dispose()");
    }

    /**
     * This method saves the model even if the spec is not parsed.  This is probably
     * a good idea, since the user may want to quit in the middle of his work without
     * losing what he's done to the model.
     * @see org.eclipse.ui.part.EditorPart#doSave(org.eclipse.core.runtime.
     * IProgressMonitor)
     */
    public void doSave(IProgressMonitor monitor)
    {
        this.commitPages(monitor, true);
        ModelHelper.doSaveConfigurationCopy(configurationCopy);

        // remove existing markers
        ModelHelper.removeModelProblemMarkers(configurationCopy, ModelHelper.TLC_MODEL_ERROR_MARKER_SANY);

        boolean revalidate = TLCUIActivator.getDefault().getPreferenceStore().getBoolean(
                ITLCPreferenceConstants.I_TLC_REVALIDATE_ON_MODIFY);
        if (revalidate)
        {
            // run SANY
            launchModel(TLCModelLaunchDelegate.MODE_GENERATE, false /*
                                                                     * the SANY
                                                                     * will run
                                                                     * only if
                                                                     * the
                                                                     * editor is
                                                                     * valid
                                                                     */);
        }

        this.editorDirtyStateChanged();
    }

    /**
     * Commits the pages and saves the config without running validation
     * on the model.
     * 
     * @param monitor
     */
    public void doSaveWithoutValidating(IProgressMonitor monitor)
    {
        this.commitPages(monitor, true);
        ModelHelper.doSaveConfigurationCopy(configurationCopy);

        this.editorDirtyStateChanged();
    }

    /**
     * @see org.eclipse.ui.part.EditorPart#doSaveAs()
     */
    public void doSaveAs()
    {
    }

    /**
     * Ask the view for an adapter for certain class
     */
    public Object getAdapter(Class required)
    {

        // ask for the launh data provider
        if (TLCModelLaunchDataProvider.class.equals(required))
        {
            // return a provider, if this can be found
            TLCModelLaunchDataProvider provider = TLCOutputSourceRegistry.getModelCheckSourceRegistry().getProvider(
                    getConfig());
            if (provider != null)
            {
                return provider;
            }
        }

        return super.getAdapter(required);
    }

    public void setFocus()
    {
        /*
         * The following commented code was causing a warning that
         * said "Prevented recursive attempt to activate part
         * toolbox.tool.tlc.view.TLCErrorView while still in the
         * middle of activating part
         * org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor"
         * 
         * The updating of the error view is now done by registering a
         * part listener in the init method of the modeleditor. This
         * part listener is an instance of ModelEditorPartListener()
         * whose partVisible() method does the updating of the
         * TLCErrorView.
         */
        // final TLCModelLaunchDataProvider provider = (TLCModelLaunchDataProvider) ModelEditor.this
        // .getAdapter(TLCModelLaunchDataProvider.class);
        // if (!provider.getErrors().isEmpty())
        // {
        // TLCErrorView errorView = (TLCErrorView) UIHelper.findView(TLCErrorView.ID);
        // if (errorView != null)
        // {
        // UIHelper.runUISync(new Runnable() {
        //
        // public void run()
        // {
        // TLCErrorView.updateErrorView(provider);
        // }
        // });
        // }
        // }
        // // TLCUIActivator.logDebug("Focusing " + getConfig().getName() +
        // // " editor");

        super.setFocus();
    }

    /*
     * @see org.eclipse.ui.part.EditorPart#isSaveAsAllowed()
     */
    public boolean isSaveAsAllowed()
    {
        return false;
    }

    /**
     * Instead of committing pages, forms and form-parts, we just commit pages 
     */
    protected void commitPages(IProgressMonitor monitor, boolean onSave)
    {
        // TLCUIActivator.logDebug("entering ModelEditor#commitPages(IProgressMonitor monitor, boolean onSave)");
        for (int i = 0; i < getPageCount(); i++)
        {
            /*
             * Note that all pages are not necessarily
             * instances of BasicFormPage. Some are read
             * only editors showing saved versions of
             * modules.
             */
            if (pages.get(i) instanceof BasicFormPage)
            {
                BasicFormPage page = (BasicFormPage) pages.get(i);
                if (page.isInitialized())
                {
                    page.commit(onSave);
                }
            }
        }
        // TLCUIActivator.logDebug("leaving ModelEditor#commitPages(IProgressMonitor monitor, boolean onSave)");
    }

    /*
     * @see org.eclipse.ui.forms.editor.FormEditor#addPages()
     */
    protected void addPages()
    {
        // TLCUIActivator.logDebug("entering ModelEditor#addPages()");
        try
        {

            // This code moves the tabs to the top of the page.
            // This makes them more obvious to the user.
            if (getContainer() instanceof CTabFolder)
            {
                ((CTabFolder) getContainer()).setTabPosition(SWT.TOP);
                ((CTabFolder) getContainer()).addCTabFolder2Listener(listener);
            } else
            {
                TLCUIActivator.logDebug("The model editor container is not a CTabFolder. This is a bug.");
            }

            for (int i = 0; i < pagesToAdd.length; i++)
            {
                addPage(pagesToAdd[i]);
                // initialize the page

                // this means the content will be created
                // the data will be loaded
                // the refresh method will update the UI state
                // the dirty listeners will be activated
                if (pagesToAdd[i].getPartControl() == null)
                {
                    pagesToAdd[i].createPartControl(getContainer());
                    setControl(i, pagesToAdd[i].getPartControl());
                    pagesToAdd[i].getPartControl().setMenu(getContainer().getMenu());
                }
            }

            // at this point everything is activated and initialized.
            // run the validation
            UIHelper.runUIAsync(validateRunable);

        } catch (PartInitException e)
        {
            TLCUIActivator.logError("Error initializing editor", e);
        }

        ModuleNode rootModule = SemanticHelper.getRootModuleNode();
        if (rootModule != null && rootModule.getVariableDecls().length == 0
                && rootModule.getConstantDecls().length == 0)
        {
            showResultPage();
        }

        // TLCUIActivator.logDebug("leaving ModelEditor#addPages()");
    }

    /* --------------------------------------------------------------------- */

    /**
     * Launch TLC or SANY
     * @param mode
     * @param userPased true, if the action is performed on behalf of the user action (explicit click on the launch button)
     */
    public void launchModel(String mode, boolean userPased)
    {
        /*
         * The user should not be able to run the model checker
         * or generate MC files if the spec is unparsed.
         * Right now, the user will simply see an message dialog
         * that has a different message depending on whether
         * the mode is model check or generate. If the mode is
         * generate, there will be a different message depending
         * on whether the user explicitly clicked generate or
         * the generation is occurring because the preference
         * to automatically revalidate on save is selected.
         * The messages appear below.
         * 
         * It would be nice to eventually add a button
         * that allows the user to parse the spec from that dialog,
         * and if parsing succeeds, to run TLC, but right now, that
         * is not implemented.
         */
        if (Activator.isSpecManagerInstantiated())
        {
            Spec spec = Activator.getSpecManager().getSpecLoaded();
            if (spec == null || spec.getStatus() != IParseConstants.PARSED)
            {
                if (mode == TLCModelLaunchDelegate.MODE_MODELCHECK)
                {
                    MessageDialog
                            .openError(getSite().getShell(), "Model checking not allowed",
                                    "The spec status is not \"parsed\". The status must be \"parsed\" before model checking is allowed.");
                } else if (mode == TLCModelLaunchDelegate.MODE_GENERATE)
                {
                    if (userPased)
                    {
                        MessageDialog
                                .openError(getSite().getShell(), "Revalidation not allowed",
                                        "The spec status is not \"parsed\". The status must be \"parsed\" before model revalidation is allowed.");
                    } else
                    {
                        MessageDialog
                                .openError(getSite().getShell(), "Revalidation not allowed",
                                        "The model can be saved, but since the spec status is not \"parsed\" model revalidation is not allowed.");
                    }
                }
                return;
            } else
            {
                /*
                 * The spec cannot be model checked if it contains a module named
                 * MC or a module named TE. Pop-up an error message to the user
                 * and do not run TLC.
                 */
                String rootModuleName = spec.getRootModule().getName();
                if (ModelHelper.containsModelCheckingModuleConflict(rootModuleName))
                {
                    MessageDialog.openError(getSite().getShell(), "Illegal module name",
                            "Model validation and checking is not allowed on a spec containing a module named "
                                    + ModelHelper.MC_MODEL_NAME + "."
                                    + (userPased ? "" : " However, the model can still be saved."));
                    return;
                }
                if (ModelHelper.containsTraceExplorerModuleConflict(rootModuleName))
                {
                    MessageDialog.openError(getSite().getShell(), "Illegal module name",
                            "Model validation and checking is not allowed on a spec containing a module named "
                                    + ModelHelper.TE_MODEL_NAME + "."
                                    + (userPased ? "" : " However, the model can still be saved."));
                    return;
                }
            }
        } else
        {
            Activator.logDebug("The spec manager has not been instantiated. This is a bug.");
            return;
        }

        /* The pages should be validated one last time before TLC
         * is run. This is currently necessary when auto-parse spec
         * is disabled. In such cases, if the user removes a contant
         * or a definition from the spec, saves, and then later parses
         * the spec, the model pages will not be validated on parsing.
         * The removed constant should cause a validation error as should
         * the removed definition if there is an override for that
         * definition. However, validation is not called, so no error
         * is displayed to the user and the pages are all complete, so
         * the toolbox attempts to run TLC. This is incorrect, so
         * validation must occur here. This is a quick fix. A better
         * fix would be to revalidate the pages when the spec is parsed.
         * 
         * This must be run synchronously so that it finishes before
         * this method checks if the pages are complete.
         */
        UIHelper.runUISync(validateRunable);

        IProgressMonitor monitor = new NullProgressMonitor();

        // save the editor if not saved
        if (isDirty())
        {
            doSave(new SubProgressMonitor(monitor, 1));
        }

        if (!isComplete())
        {
            // user clicked launch
            if (userPased)
            {
                MessageDialog.openError(getSite().getShell(), "Model processing not allowed",
                        "The model contains errors, which should be corrected before further processing");
                return;
            }
        } else
        {

            try
            {
                // launching the config
                if (mode.equals(TLCModelLaunchDelegate.MODE_MODELCHECK))
                {
                    // if model checking, the length of time that tlc
                    // should run before the model is automatically locked
                    // must be saved from the preferences
                    int autoLockTime = TLCUIActivator.getDefault().getPreferenceStore().getInt(
                            ITLCPreferenceConstants.I_TLC_AUTO_LOCK_MODEL_TIME);
                    getConfig().setAttribute(IConfigurationConstants.LAUNCH_AUTO_LOCK_MODEL_TIME, autoLockTime);
                    getConfig().doSave();
                }
                getConfig().launch(mode, new SubProgressMonitor(monitor, 1), true);

                /*
                 * Close any tabs in this editor containing read-only
                 * versions of modules. They will be changed by the launch,
                 * regardless of the mode. We could do something more sophisticated
                 * like listening to resource changes and updating the editors
                 * when the underlying files change, but the doesn't seem worth
                 * the effort.
                 */
                for (int i = 0; i < getPageCount(); i++)
                {
                    /*
                     * The normal form pages (main model page, advanced options, results)
                     * are not text editors. We leave those pages but remove all text editors.
                     */
                    if (pages.get(i) instanceof ITextEditor)
                    {
                        removePage(i);
                    }
                }

                // clear the error view when launching the model checker but not when validating
                if (mode.equals(TLCModelLaunchDelegate.MODE_MODELCHECK))
                {
                    TLCErrorView errorView = (TLCErrorView) UIHelper.findView(TLCErrorView.ID);
                    if (errorView != null)
                    {
                        errorView.clear();
                    }
                }
            } catch (CoreException e)
            {
                TLCUIActivator.logError("Error launching the configuration " + getConfig().getName(), e);
            }
        }

    }

    /**
     * Stops TLC
     */
    public void stop()
    {
        try
        {
            if (ModelHelper.isModelRunning(getConfig()) && !ModelHelper.isModelStale(getConfig()))
            {
                Job[] runningSpecJobs = Job.getJobManager().find(getConfig());
                for (int i = 0; i < runningSpecJobs.length; i++)
                {
                    // send cancellations to all jobs...
                    runningSpecJobs[i].cancel();
                }
            }
        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error stopping the model launch", e);
        }

    }

    /**
     * Returns a working copy of the launch configuration for this model.
     * 
     * @return
     */
    public ILaunchConfigurationWorkingCopy getConfig()
    {
        return configurationCopy;
    }

    /**
     * Checks whether the pages are complete and goes to the first (in order of addition) incomplete page if any
     * @return true if all pages are complete, false otherwise
     */
    public boolean isComplete()
    {
        for (int i = 0; i < getPageCount(); i++)
        {
            /*
             * Note that all pages are not necessarily
             * instances of BasicFormPage. Some are read
             * only editors showing saved versions of
             * modules.
             */
            if (pages.get(i) instanceof BasicFormPage)
            {
                BasicFormPage page = (BasicFormPage) pages.get(i);
                if (!page.isComplete())
                {
                    setActivePage(page.getId());
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Handles the problem markers attached to the model file. For those of them having the 
     * attribute set, the error bubbles will be attached to the corresponding field 
     * 
     * <br><b>Note</b>: has to be called from UI thread
     */
    public void handleProblemMarkers(boolean switchToErrorPage)
    {
        // System.out.println("Entering ModelEditor.handleProblemMarkers()");

        int errorPageIndex = -1;
        int currentPageIndex = getActivePage();
        try
        {
            IMarker[] modelProblemMarkers = ModelHelper.getModelProblemMarker(getConfig());
            // System.out.println("Found " + modelProblemMarkers.length + " markers for " + getConfig().getName());
            DataBindingManager dm = getDataBindingManager();

            for (int j = 0; j < getPageCount(); j++)
            {
                /*
                 * Note that all pages are not necessarily
                 * instances of BasicFormPage. Some are read
                 * only editors showing saved versions of
                 * modules.
                 */
                if (pages.get(j) instanceof BasicFormPage)
                {
                    // get the current page
                    BasicFormPage page = (BasicFormPage) pages.get(j);
                    Assert.isNotNull(page.getManagedForm(), "Page not initialized, this is a bug.");

                    for (int i = 0; i < modelProblemMarkers.length; i++)
                    {
                        String attributeName = modelProblemMarkers[i].getAttribute(
                                ModelHelper.TLC_MODEL_ERROR_MARKER_ATTRIBUTE_NAME,
                                IModelConfigurationDefaults.EMPTY_STRING);

                        int bubbleType = -1;
                        if (modelProblemMarkers[i].getType().equals(ModelHelper.TLC_MODEL_ERROR_MARKER_SANY))
                        {
                            // SANY markers are errors
                            bubbleType = IMessageProvider.ERROR;
                        } else if (modelProblemMarkers[i].getType().equals(ModelHelper.TLC_MODEL_ERROR_MARKER_TLC))
                        {
                            // TLC markers are warnings
                            bubbleType = IMessageProvider.WARNING;
                        } else
                        {
                            bubbleType = IMessageProvider.INFORMATION;
                        }

                        if (ModelHelper.EMPTY_STRING.equals(attributeName))
                        {
                            String message = modelProblemMarkers[i].getAttribute(IMarker.MESSAGE,
                                    IModelConfigurationDefaults.EMPTY_STRING);
                            // no attribute, this is a global error, not bound to a particular attribute
                            // install it on the first page
                            // if it is a global TLC error, then we call addGlobalTLCErrorMessage()
                            // to add a hyperlink to the TLC Error view
                            if (bubbleType == IMessageProvider.WARNING)
                            {
                                this.pagesToAdd[0].addGlobalTLCErrorMessage("modelProblem_" + i);
                                this.pagesToAdd[1].addGlobalTLCErrorMessage("modelProblem_" + i);
                            } else
                            {
                                // else install as with other messages
                                IMessageManager mm = this.pagesToAdd[0].getManagedForm().getMessageManager();
                                mm.setAutoUpdate(false);
                                mm.addMessage("modelProblem_" + i, message, null, bubbleType);
                                mm.setAutoUpdate(true);
                            }
                        } else
                        {
                            // attribute found
                            String sectionId = dm.getSectionForAttribute(attributeName);
                            Assert.isNotNull(sectionId,
                                    "Page is either not initialized or attribute not bound, this is a bug.");

                            String pageId = dm.getSectionPage(sectionId);

                            // relevant, since the attribute is displayed on the current
                            // page
                            // if (page.getId().equals(pageId))
                            // {

                            // We now want the error message to be displayed on
                            // the header of every page, so the if statement that is commented
                            // out is no longer relevant
                            IMessageManager mm = page.getManagedForm().getMessageManager();
                            mm.setAutoUpdate(false);
                            String message = modelProblemMarkers[i].getAttribute(IMarker.MESSAGE,
                                    IModelConfigurationDefaults.EMPTY_STRING);

                            Control widget = UIHelper.getWidget(dm.getAttributeControl(attributeName));
                            if (widget != null)
                            {
                                // we set the message's data object to the page id
                                // of the attribute with the error
                                // this makes it simple to switch to that page
                                // when the user clicks on the hyperlink because
                                // the hyperlink listener recieves that message and
                                // the message contains the data object.
                                mm.addMessage("modelProblem_" + i, message, pageId, bubbleType, widget);
                            }
                            // expand the section with an error
                            dm.expandSection(sectionId);
                            mm.setAutoUpdate(true);

                            if (page.getId().equals(pageId) && errorPageIndex < j)
                            {
                                errorPageIndex = j;
                            }
                            // }
                        }
                    }
                }
            }
            if (switchToErrorPage && errorPageIndex != -1 && currentPageIndex != errorPageIndex)
            {
                // the page has a marker
                // make it active
                setActivePage(errorPageIndex);
            }

        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error retrieving model error markers", e);
        }
        // System.out.println("leaving ModelEditor.handleProblemMarkers()");
    }

    /**
     * Current helper instance
     * @return
     */
    public SemanticHelper getHelper()
    {
        return this.helper;
    }

    /**
     * Retrieves the data binding manager for this editor
     */
    public DataBindingManager getDataBindingManager()
    {
        return this.dataBindingManager;
    }

    /**
     * Retrieve the file editor input
     * @return
     */
    public FileEditorInput getFileEditorInput()
    {
        IEditorInput input = getEditorInput();
        if (input instanceof FileEditorInput)
        {
            return (FileEditorInput) input;
        } else
        {
            throw new IllegalStateException("Something weird. The editor is designed for FileEditorInputOnly");
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.lamport.tla.toolbox.tool.tlc.util.ModelHelper.IResourceProvider#
     * getResource()
     */
    public IFile getResource(int type)
    {
        IFile result = getFileEditorInput().getFile();

        switch (type) {
        case IFileProvider.TYPE_MODEL:
            break;
        case IFileProvider.TYPE_RESULT:
            String modelName = ModelHelper.getModelName(result);
            result = result.getProject().getFolder(modelName).getFile(ModelHelper.FILE_OUT);
            break;
        default:
            result = null;
            break;
        }
        return result;
    }

    /**
     * Retrieves if the working copy of the model is running
     * @return true, if the model is locked 
     */
    public boolean isModelRunning()
    {
        try
        {
            return ModelHelper.isModelRunning(getConfig());
        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error determining model status", e);
            return true;
        }
    }

    /**
     * Retrieves if the working copy of the model is locked
     * @return true, if the model is locked 
     */
    public boolean isModelLocked()
    {
        try
        {
            return ModelHelper.isModelLocked(getConfig());
        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error determining model status", e);
            return true;
        }
    }

    /**
     * Retrieves if the working copy of the model is still left 
     * in in-use status, even if no process is running on it anymore
     */
    public boolean isModelStale()
    {
        try
        {
            return ModelHelper.isModelStale(getConfig());
        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error determining model status", e);
            return true;
        }
    }

    /**
     * Show the result page of the editor    
     */
    public void showResultPage()
    {
        // goto result page
        IFormPage resultPage = setActivePage(ResultPage.ID);
        if (resultPage != null)
        {
            try
            {
                ((ResultPage) resultPage).loadData();
            } catch (CoreException e)
            {
                TLCUIActivator.logError("Error refreshing the result page", e);
            }
        }
    }

    // TODO remove
    public void setUpPage(BasicFormPage newPage, int index)
    {
        if (newPage.getPartControl() == null)
        {
            newPage.createPartControl(this.getContainer());
            setControl(index, newPage.getPartControl());
            newPage.getPartControl().setMenu(getContainer().getMenu());
        }
    }

    /**
     * This adds error messages to all pages for the given control.
     * If the control is null, it will do nothing.
     * 
     * @param key the unique message key
     * @param messageText the message to add
     * @param pageId the id of the page that contains the control
     * @param type the message type
     * @param control the control to associate the message with
     */
    public void addErrorMessage(Object key, String messageText, String pageId, int type, Control control)
    {
        if (control != null)
        {
            for (int i = 0; i < pagesToAdd.length; i++)
            {
                pagesToAdd[i].getManagedForm().getMessageManager().addMessage(key, messageText, pageId, type, control);
            }
        }
    }

    /**
     * Returns the validateRunnable so that the pages
     * can be validated by code outside of this class.
     * @return
     */
    public ValidateRunnable getValidateRunnable()
    {
        return validateRunable;
    }

    /**
     * Overrides the method in {@link FormEditor}. Calls this method in the superclass
     * and then makes some changes if the input is a tla file.
     * 
     * This is done so that when read-only editor pages are added to this model editor,
     * we can make the following changes:
     * 
     * 1.) Set the title of the tabs of those pages to the name of the module being shown.
     *    If this is not done, the title of those tabs would be the empty string.
     *    
     * 2.) Set those pages to be closeable. This makes it possible to click on the tab
     *     to close it.
     */
    public void addPage(int index, IEditorPart editor, IEditorInput input) throws PartInitException
    {
        super.addPage(index, editor, input);
        /*
         * Do stuff if the input is a tla file.
         * 
         * 1.) Set the title of the page to be the
         * name of the file.
         * 
         * 2.) Set the page to be closeable.
         */
        if (input instanceof FileEditorInput
                && ((FileEditorInput) input).getFile().getFileExtension().equals(ResourceHelper.TLA_EXTENSION))
        {
            setPageText(index, input.getName());
            /*
             * When I implemented this method, getContainer()
             * returned a CTabFolder. If this somehow stops
             * being the case, then I do not know how to set
             * the tla file pages to be closeable.
             */
            if (getContainer() instanceof CTabFolder)
            {
                ((CTabFolder) getContainer()).getItem(index).setShowClose(true);

            }
            // setPageImage(pageIndex, image);
        }
    }

    /**
     * A listener that reacts to when editor tabs showing saved modules
     * get closed. This listener blocks the underlying folder widget
     * from directly closing the page. Instead, it calls the
     * {@link ModelEditor#removePage(int)} method to remove the page.
     * This properly disposes of the editor. If the editor page is not
     * removed this way, bad things happen, like memory leaks and bizarre
     * problems updating the editor contents.
     * 
     * @author Daniel Ricketts
     *
     */
    private class CloseModuleTabListener extends CTabFolder2Adapter
    {

        public void close(CTabFolderEvent event)
        {
            Assert
                    .isTrue(event.item instanceof CTabItem,
                            "Something other than a CTabItem was closed in a CTabFolder.");
            CTabItem item = (CTabItem) event.item;

            // block the CTabFolder from directly removing the tab
            event.doit = false;

            // remove the page properly
            removePage(item.getParent().indexOf(item));
        }
    }
}
