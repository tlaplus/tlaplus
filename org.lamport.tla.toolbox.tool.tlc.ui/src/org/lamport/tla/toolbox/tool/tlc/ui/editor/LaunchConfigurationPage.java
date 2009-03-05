package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.lamport.tla.toolbox.util.IHelpConstants;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class LaunchConfigurationPage extends BasicFormPage
{

    public static final String ID = "LaunchConfiguration";

    public LaunchConfigurationPage(FormEditor editor)
    {
        super(editor, LaunchConfigurationPage.ID, "Launch Configuration");
        this.helpId = IHelpConstants.LAUNCH_MODEL_PAGE; 
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.ui.editor.BasicFormPage#createContent(org.eclipse.ui.forms.widgets.FormToolkit, org.eclipse.swt.widgets.Composite)
     */
    protected void createContent(FormToolkit toolkit, Composite body)
    {
        
    }

    
}
