package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.lamport.tla.toolbox.util.IHelpConstants;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class GeneralModelPage extends BasicFormPage
{

    public static final String ID = "GeneralModelPage";

    public GeneralModelPage(FormEditor editor)
    {
        super(editor, GeneralModelPage.ID, "Model Summary");
        
        this.helpId = IHelpConstants.GENERAL_MODEL_PAGE;
    }


    protected void createContent(FormToolkit toolkit, Composite parent) 
    {
        
    }
}
