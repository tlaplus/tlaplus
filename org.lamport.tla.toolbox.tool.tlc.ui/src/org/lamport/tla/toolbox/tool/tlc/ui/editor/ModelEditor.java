package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.AdvancedModelPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.BasicFormPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.IDoRunContainer;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.MainModelPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.ResultPage;
import org.lamport.tla.toolbox.tool.tlc.ui.util.SemanticHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Editor for the model
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelEditor extends FormEditor
{
    public static final String ID = "org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor";
    private ILaunchConfigurationWorkingCopy configurationCopy;
    private SemanticHelper helper;

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
                        Object page = pages.get(i);
                        if (page instanceof ISectionManager)
                        {
                            BasicFormPage bPage = (BasicFormPage) page;
                            // re-validate the model on changes of the spec
                            bPage.validate();
                        }
                    }
                }
            });
        }
    };

    private IResourceChangeListener modelFileListener = new IResourceChangeListener() {
        public void resourceChanged(IResourceChangeEvent event)
        {
            FileEditorInput finput = getFileEditorInput();
            IResourceDelta findMember = event.getDelta().findMember(finput.getFile().getFullPath());
            if (findMember != null)
            {
                UIHelper.runUIAsync(new Runnable() {
                    public void run()
                    {
                        // update the tool bar
                        if (pages != null)
                        {
                            for (int i = 0; i < pages.size(); i++)
                            {
                                Object page = pages.get(i);
                                if (page instanceof BasicFormPage)
                                {
                                    ((BasicFormPage) page).refresh();
                                }
                            }
                        }
                    }
                });
            }
        }
    };

    // section manager
    private SectionManager sectionManager = new SectionManager();

    public ModelEditor()
    {
        helper = new SemanticHelper();
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
             * Install a resource change listener on the file opened
             * Update the information from the file is the file changes
             */
            ResourcesPlugin.getWorkspace().addResourceChangeListener(modelFileListener,
                    IResourceChangeEvent.POST_CHANGE);
            // setContentDescription(path.toString());
            setPartName(ModelHelper.getModelName(finput.getFile()));
            setTitleToolTip(finput.getFile().getProjectRelativePath().toString());
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
                    Object page = pages.get(i);
                    if (page instanceof ISectionManager)
                    {
                        BasicFormPage bPage = (BasicFormPage) page;
                        // re-validate the model on changes of the spec
                        bPage.validate();
                    }
                }
            }
        });

    }

    public void dispose()
    {
        // remove the listeners
        ResourcesPlugin.getWorkspace().removeResourceChangeListener(rootFileListener);
        ResourcesPlugin.getWorkspace().removeResourceChangeListener(modelFileListener);
        super.dispose();
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.part.EditorPart#doSave(org.eclipse.core.runtime.IProgressMonitor)
     */
    public void doSave(IProgressMonitor monitor)
    {
        this.commitPages(monitor, true);
        ModelHelper.doSaveConfigurationCopy(configurationCopy);
        this.editorDirtyStateChanged();
    }

    /**
     * Instead of committing pages, forms and form-parts, we just commit pages 
     */
    protected void commitPages(IProgressMonitor monitor, boolean onSave)
    {
        if (pages != null)
        {
            for (int i = 0; i < pages.size(); i++)
            {
                Object page = pages.get(i);

                if (page instanceof BasicFormPage)
                {
                    BasicFormPage fpage = (BasicFormPage) page;
                    if (fpage.isInitialized())
                    {
                        fpage.commit(onSave);
                    }
                }
            }
        }
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.part.EditorPart#doSaveAs()
     */
    public void doSaveAs()
    {
        System.out.println("SaveAs called");

    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.part.EditorPart#isSaveAsAllowed()
     */
    public boolean isSaveAsAllowed()
    {
        return true;
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.forms.editor.FormEditor#addPages()
     */
    protected void addPages()
    {
        try
        {
            addPage(new MainModelPage(this));
            addPage(new AdvancedModelPage(this));
            addPage(new ResultPage(this));

        } catch (PartInitException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    public ILaunchConfigurationWorkingCopy getConfig()
    {
        return configurationCopy;
    }

    /**
     * @return
     */
    public boolean isComplete()
    {
        for (int i = 0; i < pages.size(); i++)
        {
            Object page = pages.get(i);
            if (page instanceof IDoRunContainer)
            {
                BasicFormPage bPage = (BasicFormPage) page;
                if (!bPage.isComplete())
                {
                    setActivePage(bPage.getId());
                    return false;
                }
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
            throw new IllegalStateException("Something wierd. The editor is designed for FileEditorInputOnly");
        }
    }
}
