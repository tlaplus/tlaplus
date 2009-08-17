package org.lamport.tla.toolbox.tool.tlc.ui;

import org.eclipse.debug.core.ILaunchConfiguration;
import org.lamport.tla.toolbox.tool.tlc.result.IResultPresenter;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Responsible for presenting the TLC launch results
 * 
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ResultPresenter implements IResultPresenter
{

    public ResultPresenter()
    {
    }

    public void showResults(ILaunchConfiguration configuration)
    {
        ModelEditor editor = (ModelEditor) UIHelper.openEditor(ModelEditor.ID, configuration.getFile());
        if (editor != null) 
        {
            editor.showResultPage();
        }
    }

}
