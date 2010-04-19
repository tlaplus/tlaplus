package org.lamport.tla.toolbox.tool.prover.ui.handler;

import java.util.HashMap;

import javax.print.attribute.HashAttributeSet;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.texteditor.ITextEditor;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

public class CheckProofStepHandlerDelegate extends AbstractHandler implements IHandler
{

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        ISelection selection = UIHelper.getActivePage().getSelection();
        IEditorPart editor = HandlerUtil.getActiveEditor(event);
        // ISelection selection = UIHelper.getActiveEditorFileSelectionProvider().getSelection();
        if (selection instanceof ITextSelection)
        {
            ITextSelection textSelection = (ITextSelection) selection;
            int line = textSelection.getEndLine();
            IEditorInput edInput = editor.getEditorInput();
            String moduleFileName = edInput.getName();
            HashMap params = new HashMap();
            params.put(CheckProofStepHandler.PARAM_MODULE_NAME, moduleFileName.substring(0, moduleFileName.indexOf("."
                    + ResourceHelper.TLA_EXTENSION)));
            params.put(CheckProofStepHandler.PARAM_LINE_NUMBER, String.valueOf(line));

            UIHelper.runCommand(CheckProofStepHandler.COMMAND_ID, params);
        }
        return null;
    }
}
