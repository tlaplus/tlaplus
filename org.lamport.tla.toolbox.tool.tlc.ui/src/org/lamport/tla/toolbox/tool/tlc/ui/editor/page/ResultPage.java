package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import org.eclipse.ui.forms.editor.FormEditor;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ResultPage extends BasicFormPage
{

    public static final String ID = "resultPage";
    /**
     * @param editor
     * @param id
     * @param title
     */
    public ResultPage(FormEditor editor)
    {
        super(editor, ID, "Model Checking Results");
    }

}
