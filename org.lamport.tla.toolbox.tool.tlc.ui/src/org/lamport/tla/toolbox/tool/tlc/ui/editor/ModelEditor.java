package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
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
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.forms.IMessageManager;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.AdvancedModelPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.BasicFormPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.MainModelPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.ResultPage;
import org.lamport.tla.toolbox.tool.tlc.ui.preference.ITLCPreferenceConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.util.SemanticHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper.IFileProvider;
import org.lamport.tla.toolbox.util.UIHelper;

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

    private Runnable validateRunable = new Runnable() {
        public void run()
        {
            for (int i = 0; i < getPageCount(); i++)
            {
                BasicFormPage page = (BasicFormPage) pages.get(i);
                // re-validate the model on changes of the spec
                page.validate();
            }
        }
    };

    // react on spec root file changes
    private IResourceChangeListener rootFileListener = new IResourceChangeListener() {
        public void resourceChanged(IResourceChangeEvent event)
        {
            // update the specObject of the helper
            helper.resetSpecNames();

            // re-validate the pages
            UIHelper.runUIAsync(validateRunable);
        }
    };

    // section manager
    private DataBindingManager dataBindingManager = new DataBindingManager();

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
             * Install a resource change listener on the file opened which react on marker changes
             */
            modelFileChangeListener = ModelHelper.installModelModificationResourceChangeListener(this,
            /* 
             * If the model file is changed, refresh the changes in the editor
             * if the model is in use, activate the third page 
             */
            new Runnable() {
                public void run()
                {
                    // update the pages
                    for (int i = 0; i < getPageCount(); i++)
                    {
                        BasicFormPage page = (BasicFormPage) pages.get(i);
                        ((BasicFormPage) page).refresh();
                    }

                    if (isModelInUse())
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
        }

        /*
         * Install resource change listener on the root file of the specification
         * react on changes of the root file
         */
        ResourcesPlugin.getWorkspace().addResourceChangeListener(rootFileListener, IResourceChangeEvent.POST_BUILD);

        // update the spec object of the helper
        helper.resetSpecNames();

        // initial re-validate the pages, which are already loaded
        UIHelper.runUIAsync(validateRunable);
        // TLCUIActivator.logDebug("leaving ModelEditor#init(IEditorSite site, IEditorInput input)");
    }

    /*
     * @see org.eclipse.ui.forms.editor.FormEditor#dispose()
     */
    public void dispose()
    {
        // TLCUIActivator.logDebug("entering ModelEditor#dispose()");
        // remove the listeners
        ResourcesPlugin.getWorkspace().removeResourceChangeListener(rootFileListener);
        ResourcesPlugin.getWorkspace().removeResourceChangeListener(modelFileChangeListener);
        super.dispose();
        // TLCUIActivator.logDebug("leaving ModelEditor#dispose()");
    }

    /* 
     * @see org.eclipse.ui.part.EditorPart#doSave(org.eclipse.core.runtime.IProgressMonitor)
     */
    public void doSave(IProgressMonitor monitor)
    {
        this.commitPages(monitor, true);
        ModelHelper.doSaveConfigurationCopy(configurationCopy);

        // remove existing markers
        ModelHelper.removeModelProblemMarkers(configurationCopy);

        boolean revalidate = TLCUIActivator.getDefault().getPreferenceStore().getBoolean(
                ITLCPreferenceConstants.I_TLC_REVALIDATE_ON_MODIFY);
        if (revalidate)
        {
            // run SANY
            launchModel(TLCModelLaunchDelegate.MODE_GENERATE, false /* the SANY will run only if the editor is valid */);
        }

        this.editorDirtyStateChanged();
    }

    /* 
     * @see org.eclipse.ui.part.EditorPart#doSaveAs()
     */
    public void doSaveAs()
    {
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
            BasicFormPage page = (BasicFormPage) pages.get(i);
            if (page.isInitialized())
            {
                page.commit(onSave);
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

            // launching the config
            try
            {
                getConfig().launch(mode, new SubProgressMonitor(monitor, 1), true);
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
            if (ModelHelper.isModelLocked(getConfig()) && !ModelHelper.isModelStale(getConfig()))
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
            BasicFormPage page = (BasicFormPage) pages.get(i);
            if (!page.isComplete())
            {
                setActivePage(page.getId());
                return false;
            }
        }
        return true;
    }

    /**
     * Handles the problem markers
     * 
     */
    public void handleProblemMarkers()
    {
        int errorPageIndex = -1;
        int currentPageIndex = getActivePage();
        try
        {
            IMarker[] modelProblemMarkers = ModelHelper.getModelProblemMarker(getConfig());
            DataBindingManager dm = getDataBindingManager();

            for (int j = 0; j < getPageCount(); j++)
            {
                // get the current page
                BasicFormPage page = (BasicFormPage) pages.get(j);
                Assert.isNotNull(page.getManagedForm(), "Page not initialized, this is a bug.");
                
                for (int i = 0; i < modelProblemMarkers.length; i++)
                {
                    String attributeName = modelProblemMarkers[i]
                            .getAttribute(ModelHelper.TLC_MODEL_ERROR_MARKER_ATTRIBUTE_NAME,
                                    IModelConfigurationDefaults.EMPTY_STRING);
                    String sectionId = dm.getSectionForAttribute(attributeName);
                    Assert.isNotNull(sectionId, "Page is either not initialized or attribute not bound, this is a bug.");

                    String pageId = dm.getSectionPage(sectionId);
                    
                    // relevant, since the attribute is displayed on the current page
                    if (page.getId().equals(pageId))
                    {
                        IMessageManager mm = page.getManagedForm().getMessageManager();
                        mm.setAutoUpdate(false);
                        String message = modelProblemMarkers[i].getAttribute(IMarker.MESSAGE,
                                IModelConfigurationDefaults.EMPTY_STRING);

                        Control widget = UIHelper.getWidget(dm.getAttributeControl(attributeName));
                        if (widget != null)
                        {
                            mm.addMessage("modelProblem_" + i, message, null, IMessageProvider.ERROR, widget);
                        }
                        // expand the section with an error
                        dm.expandSection(sectionId);
                        mm.setAutoUpdate(true);
                        
                        if (errorPageIndex < j) 
                        {
                            errorPageIndex = j;
                        }
                    }
                }
            }
            if (errorPageIndex != -1 && currentPageIndex != errorPageIndex) 
            {
                // the page has a marker
                // make it active
                setActivePage(errorPageIndex);
            }
            

        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error retrieving model error markers", e);
        }

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

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.util.ModelHelper.IResourceProvider#getResource()
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
     * Retrieves if the working copy of the model is in use
     * @return true, if the model is locked 
     */
    public boolean isModelInUse()
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
        setActivePage(ResultPage.ID);
    }

}
