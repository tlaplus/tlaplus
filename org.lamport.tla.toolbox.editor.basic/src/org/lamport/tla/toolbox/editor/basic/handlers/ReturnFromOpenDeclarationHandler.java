/**
 * 
 */
package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.text.ITextSelection;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * @author lamport
 *
 */
public class ReturnFromOpenDeclarationHandler extends AbstractHandler implements IHandler
{

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        Spec spec = ToolboxHandle.getCurrentSpec();
        String fileName = spec.getOpenDeclModuleName();
        ITextSelection its = spec.getOpenDeclSelection();
        if ((fileName != null) && (its != null))
        {
            UIHelper.jumpToSelection(fileName, spec.getOpenDeclSelection());
        }
        ;
        return null;
    }

}
