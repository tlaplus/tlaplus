package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

/**
 * Editor for the model
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelEditor extends FormEditor
{
    public static final String ID = "org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor";
    private ILaunchConfigurationWorkingCopy configurationCopy;

    public ModelEditor()
    {

    }

    public void init(IEditorSite site, IEditorInput input) throws PartInitException
    {
        super.init(site, input);
        if (input instanceof FileEditorInput)
        {
            FileEditorInput finput = (FileEditorInput) input;
            if (finput != null)
            {
                ILaunchConfiguration configuration = ModelHelper.getModelByFile(finput.getFile());
                try
                {
                    configurationCopy = configuration.getWorkingCopy();
                } catch (CoreException e)
                {
                    e.printStackTrace();
                }

                IPath path = finput.getPath();
                // setContentDescription(path.toString());
                setPartName(path.removeFileExtension().lastSegment());
                setTitleToolTip(path.toString());
            }
        }

    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.part.EditorPart#doSave(org.eclipse.core.runtime.IProgressMonitor)
     */
    public void doSave(IProgressMonitor monitor)
    {
        // System.out.println("Save called");
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
                    IManagedForm mform = fpage.getManagedForm();
                    if (mform != null && mform.isDirty())
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
            /*
            addPage(new GeneralModelPage(this));
            addPage(new BehaviorFormulaPage(this));
            addPage(new CorrectnessPage(this));
            addPage(new ParametersPage(this));
            addPage(new ModelValuesPage(this));
            */
            addPage(new MainModelPage(this));

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

}
