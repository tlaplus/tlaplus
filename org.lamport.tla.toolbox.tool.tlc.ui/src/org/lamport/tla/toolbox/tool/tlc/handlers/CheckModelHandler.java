package org.lamport.tla.toolbox.tool.tlc.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.forms.editor.IFormPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.BasicFormPage;
import org.lamport.tla.toolbox.util.UIHelper;

public class CheckModelHandler extends AbstractHandler
{

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.AbstractHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        IEditorPart activeEditor = UIHelper.getActiveEditor();
        if (activeEditor != null)
        {
            if (activeEditor instanceof ModelEditor)
            {
                ModelEditor activeModelEditor = (ModelEditor) activeEditor;
                IFormPage page = activeModelEditor.getActivePageInstance();
                if (page instanceof BasicFormPage)
                {
                    BasicFormPage activePage = (BasicFormPage) page;
                    activePage.doRun();
                }
            }
        }
        return null;
    }

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#isEnabled()
	 */
	@Override
	public boolean isEnabled() {
		if (UIHelper.getActiveEditor() == null) {
			return false;
		}
		return super.isEnabled();
	}
}
