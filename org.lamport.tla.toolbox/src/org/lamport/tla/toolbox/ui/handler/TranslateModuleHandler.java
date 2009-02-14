package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.lamport.tla.toolbox.util.UIHelper;

import pcal.TranslatorLauncher;
/**
 * Triggers the PCal translation of the module
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TranslateModuleHandler extends AbstractHandler implements IHandler
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
            System.out.println(fileToBuild.getLocation().toOSString());
            
            TranslatorLauncher.runPcalTranslation(new String[]{fileToBuild.getLocation().toOSString()});
            
            
            try
            {
                fileToBuild.refreshLocal(IResource.DEPTH_ONE, null);
            } catch (CoreException e)
            {
                // TODO
                e.printStackTrace();
            }
            
        } 

        
        
        return null;
    }

}
