package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.editor.IFormPage;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.AdvancedModelPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.BasicFormPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.MainModelPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.ResultPage;
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

    // reacts on changes of the output file
    private IResourceChangeListener outputFileChangeListener;

    // react on spec root file changes
    private IResourceChangeListener rootFileListener = new IResourceChangeListener() {
        public void resourceChanged(IResourceChangeEvent event)
        {
            // update the specObject of the helper
            helper.resetSpecNames();

            // re-validate the pages
            UIHelper.runUIAsync(new Runnable() {
                public void run()
                {
                    for (int i = 0; i < getPageCount(); i++)
                    {
                        BasicFormPage page = (BasicFormPage) pages.get(i);
                        // re-validate the model on changes of the spec
                        page.validate();
                    }
                }
            });
        }
    };

    // section manager
    private SectionManager sectionManager = new SectionManager();

    private ResultPage resultPage;

    /**
     * Simple editor constructor
     */
    public ModelEditor()
    {
        helper = new SemanticHelper();
        resultPage = new ResultPage(this);
    }

    /**
     * Initialize the editor
     */
    public void init(IEditorSite site, IEditorInput input) throws PartInitException
    {
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
                        // goto result page
                        setActivePage(ResultPage.ID);
                    }
                    // TODO evtl. add more graphical sugar here,
                    // like changing the model icon, 
                    // changing the editor title (part name)
                }
            });

            /*
             * Install a resource change listener on the output file
             * Update the information from the file is the file changes
             */
            ResourcesPlugin.getWorkspace().addResourceChangeListener(resultPage, IResourceChangeEvent.POST_CHANGE);

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

        // initial re-validate the pages
        UIHelper.runUIAsync(new Runnable() {
            public void run()
            {
                // since validation is cheap and we are interested in
                for (int i = 0; i < getPageCount(); i++)
                {
                    BasicFormPage page = (BasicFormPage) pages.get(i);
                    // re-validate the model on changes of the spec
                    page.validate();
                }
            }
        });

    }

    /*
     * @see org.eclipse.ui.forms.editor.FormEditor#dispose()
     */
    public void dispose()
    {
        // remove the listeners
        ResourcesPlugin.getWorkspace().removeResourceChangeListener(rootFileListener);
        ResourcesPlugin.getWorkspace().removeResourceChangeListener(modelFileChangeListener);
        ResourcesPlugin.getWorkspace().removeResourceChangeListener(resultPage);
        super.dispose();
    }

    /* 
     * @see org.eclipse.ui.part.EditorPart#doSave(org.eclipse.core.runtime.IProgressMonitor)
     */
    public void doSave(IProgressMonitor monitor)
    {
        this.commitPages(monitor, true);
        ModelHelper.doSaveConfigurationCopy(configurationCopy);
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
        for (int i = 0; i < getPageCount(); i++)
        {
            BasicFormPage page = (BasicFormPage) pages.get(i);
            if (page.isInitialized())
            {
                page.commit(onSave);
            }
        }
    }

    /*
     * @see org.eclipse.ui.forms.editor.FormEditor#addPages()
     */
    protected void addPages()
    {
        try
        {
            addPage(new MainModelPage(this));
            addPage(new AdvancedModelPage(this));
            addPage(resultPage);

        } catch (PartInitException e)
        {
            TLCUIActivator.logError("Error initializing editor", e);
        }
    }

    public ILaunchConfigurationWorkingCopy getConfig()
    {
        return configurationCopy;
    }

    /**
     * Checks weather the pages are complete and goes to the first (in order of addition) incomplete page if any
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
     * Current helper instance
     * @return
     */
    public SemanticHelper getHelper()
    {
        return this.helper;
    }

    /**
     * @return
     */
    public SectionManager getSectionManager()
    {
        return this.sectionManager;
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
            result = result.getProject().getFolder(modelName).getFile("MC.out");
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

}
