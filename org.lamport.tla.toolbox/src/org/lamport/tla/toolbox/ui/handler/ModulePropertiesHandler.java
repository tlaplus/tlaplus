package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IResource;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.ISelectionService;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModulePropertiesHandler extends AbstractHandler implements IHandler
{

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
     
        System.out.println("Module Props");
        
        IEditorInput editorInput = UIHelper.getActivePage().getActiveEditor().getEditorInput();
        if (editorInput instanceof IFileEditorInput) 
        {
            IResource openedFile = ((IFileEditorInput) editorInput).getFile();
            
            ISelectionService service = UIHelper.getActiveWindow().getSelectionService();
            
            
        }
        
        
        return null;
    }

}
