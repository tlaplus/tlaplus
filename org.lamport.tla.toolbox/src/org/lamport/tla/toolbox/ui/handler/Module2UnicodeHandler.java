package org.lamport.tla.toolbox.ui.handler;

import java.io.StringReader;
import java.io.StringWriter;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.ui.texteditor.ITextEditor;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2unicode.TLAUnicode;

/**
 * Parses the current module in the editor
 * @author Ron Pressler (pron)
 * @version $Id$
 */
public class Module2UnicodeHandler extends SaveDirtyEditorAbstractHandler implements IHandler {

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.AbstractHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException {
        if (event.getCommand() == null)
        	return null;
        if (!(UIHelper.getActiveEditor() instanceof ITextEditor))
        	return null;
        
        final ITextEditor activeEditor = (ITextEditor)UIHelper.getActiveEditor();
        final IEditorInput editorInput = activeEditor.getEditorInput();

        switch (event.getCommand().getId()) {
        case "toolbox.command.module.a2u.active":
        	if (editorInput instanceof IStorageEditorInput) { // IFileEditorInput
            	// final IStorageEditorInput input1 = (IStorageEditorInput)editorInput;
        		final IDocument doc = activeEditor.getDocumentProvider().getDocument(editorInput);
            	final StringWriter out = new StringWriter();
            	TLAUnicode.convert(true, new StringReader(doc.get()), out);
            	
            	doc.set(out.toString());
            }
        	
        case "toolbox.command.module.exportascii.active":
        	if (!saveDirtyEditor(event))
        		return null;
        	
            // prompt to save any unsaved resources
            if (!UIHelper.promptUserForDirtyModules())
                return null;
            final IResource fileToBuild = ((IFileEditorInput) editorInput).getFile();
            
        default:
        	return null;
        }
    }

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#isEnabled()
	 */
	@Override
	public boolean isEnabled() {
		if (UIHelper.getActiveEditor() == null)
			return false;
		return super.isEnabled();
	}
}
