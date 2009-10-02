package org.lamport.tla.toolbox.tool.tla2tex.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IResource;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2tex.TLA;

/**
 * 
 * @author Daniel Ricketts
 * @version $Id$
 */
public class ProducePDFHandler extends AbstractHandler
{

    public Object execute(ExecutionEvent event)
    {
        System.out.println("PDF Handler executed.");
        // TODO Auto-generated method stub

        IEditorPart activeEditor = UIHelper.getActivePage().getActiveEditor();

        if (activeEditor.isDirty())
        {
            // editor is not saved
            // TODO react on this!
        }

        IEditorInput editorInput = activeEditor.getEditorInput();
        if (editorInput instanceof IFileEditorInput)
        {
            IResource fileToTranslate = ((IFileEditorInput) editorInput).getFile();
            if (fileToTranslate != null && ResourceHelper.isModule(fileToTranslate))
            {
                System.out.println(fileToTranslate.getLocation().toOSString());
                TLA.runTranslation(new String[] {fileToTranslate.getLocation().toOSString()});
            }
        }

        return null;
    }

}
