package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.ui.forms.editor.FormEditor;
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
}
