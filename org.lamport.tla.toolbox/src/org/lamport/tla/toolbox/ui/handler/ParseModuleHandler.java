package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.nature.ParserHelper;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
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
        IEditorPart activeEditor = UIHelper.getActiveEditor();

        // if (activeEditor.isDirty())
        // {
        // // editor is not saved
        // // TODO react on this!
        // }

        // prompt to save any unsaved resources
        // the module open in the active editor could be dependent upon
        // any open module
        boolean proceed = UIHelper.promptUserForDirtyModules();
        if (!proceed)
        {
            return null;
        }

        IEditorInput editorInput = activeEditor.getEditorInput();
        if (editorInput instanceof IFileEditorInput)
        {
            IResource fileToBuild = ((IFileEditorInput) editorInput).getFile();
            // explicitly invoke the module rebuild
            // if the module is the root module, rebuild the spec (and change the status afterwards)
            Spec currentSpec = ToolboxHandle.getCurrentSpec();
            if (currentSpec != null && currentSpec.getRootFile().equals(fileToBuild))
            {
                ParserHelper.rebuildSpec(new NullProgressMonitor());
            } else
            {
                ParserHelper.rebuildModule(fileToBuild, new NullProgressMonitor());
            }
        }

        return null;
    }
}
