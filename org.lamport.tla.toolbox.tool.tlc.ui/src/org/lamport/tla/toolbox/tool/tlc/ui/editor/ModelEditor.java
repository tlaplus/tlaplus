package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.forms.editor.FormEditor;

/**
 * Editor for the model
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelEditor extends FormEditor
{
    public static final String ID = "org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor";

    public ModelEditor()
    {
        
    }


    /* (non-Javadoc)
     * @see org.eclipse.ui.forms.editor.FormEditor#addPages()
     */
    protected void addPages()
    {
        try
        {
            // addPage(new GeneralModelPage(this));
            addPage(new BehaviorFormulaPage(this));
            addPage(new CorrectnessPage(this));
            addPage(new ParametersPage(this));
            addPage(new ModelValuesPage(this));
            addPage(new LaunchConfigurationPage(this));
            
        } catch (PartInitException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.part.EditorPart#doSave(org.eclipse.core.runtime.IProgressMonitor)
     */
    public void doSave(IProgressMonitor monitor)
    {

    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.part.EditorPart#doSaveAs()
     */
    public void doSaveAs()
    {

    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.part.EditorPart#isSaveAsAllowed()
     */
    public boolean isSaveAsAllowed()
    {
        return false;
    }

}
