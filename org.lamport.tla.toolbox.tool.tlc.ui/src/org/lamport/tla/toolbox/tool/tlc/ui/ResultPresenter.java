package org.lamport.tla.toolbox.tool.tlc.ui;

import org.lamport.tla.toolbox.tool.tlc.launch.TraceExplorerDelegate;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.result.IResultPresenter;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.view.TLCErrorView;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Responsible for presenting the TLC launch results
 * 
 * @author Simon Zambrovski
 */
public class ResultPresenter implements IResultPresenter {
	public void showResults(Model model) {
        /*
         * For trace exploration, just update the error view with the data
         * from the run of TLC for trace exploration. For model checking, open
         * the editor for that model, show the result page, and update the
         * data on the result page.
         */
		if (model.getLastLaunch().getLaunchMode().equals(TraceExplorerDelegate.MODE_TRACE_EXPLORE)) {
            final ModelEditor modelEditor = model.getAdapter(ModelEditor.class);
			if ((modelEditor != null) && (modelEditor.getActivePage() != -1)) {
                // If an editor is open and active on the model, update the error view.
                // Although the trace explorer only takes a few seconds to run,
                // the user could still switch to another model.
                // If so, this code should not be run.
                TLCErrorView.updateErrorView(modelEditor);
            }
		} else {
			final ModelEditor editor = (ModelEditor) UIHelper.openEditor(ModelEditor.ID, model.getFile());
			if (editor != null) {
                editor.addOrShowResultsPage();
            }
        }
    }
}
