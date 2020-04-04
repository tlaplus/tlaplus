package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.Spec.Pair;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.UIHelper;

public class ReturnFromOpenDeclarationHandler extends AbstractHandler implements IHandler
{

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        final Spec spec = ToolboxHandle.getCurrentSpec();
        final Pair p = spec.getOpenDeclModuleName();
		if (p != null) {
			UIHelper.jumpToSelection(p.editor, p.selection);
			//TODO Bring the editor back to top in its editor stack.
		}
        return null;
    }

}
