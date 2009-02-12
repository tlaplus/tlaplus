package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IResource;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.lamport.tla.toolbox.spec.nature.ParserHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Parses the current module in the editor
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParseModuleHandler extends AbstractHandler implements IHandler
{

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        IEditorPart activeEditor = UIHelper.getActivePage().getActiveEditor();
        
        if (activeEditor.isDirty()) 
        {
            // editor is not saved
            // TODO react on this!
        }
        
        IEditorInput editorInput = activeEditor.getEditorInput();
        if (editorInput instanceof IFileEditorInput)
        {
            IResource fileToBuild = ((IFileEditorInput)editorInput).getFile();
            ParserHelper.rebuildModule(fileToBuild, null);
        } 
        
        
        return null;
    }
}
