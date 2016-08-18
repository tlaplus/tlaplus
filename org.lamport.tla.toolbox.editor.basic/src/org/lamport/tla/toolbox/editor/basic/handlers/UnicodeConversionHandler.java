package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.swt.widgets.Shell;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.ui.preference.EditorPreferencePage;
import org.lamport.tla.toolbox.util.StringHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2unicode.Unicode;

/**
 * This is the handler method for the following commands:
 * 
 * Convert selection to Unicode
 * Convert selection to ASCII
 * 
 * 
 * @author pron
 * 
 */
public class UnicodeConversionHandler extends AbstractHandler implements IHandler {
	/*
	 * Command ids.
	 */
	public static final String ID_CONVERT_SELECTION_TO_UNICODE = "org.lamport.tla.toolbox.editor.basic.convertToUnicode";
	public static final String ID_CONVERT_SELECTION_TO_ASCII = "org.lamport.tla.toolbox.editor.basic.convertToASCII";

	
	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.
	 * ExecutionEvent)
	 */
	public Object execute(ExecutionEvent event) throws ExecutionException {
		final TLAEditor editor = EditorUtil.getTLAEditorWithFocus();
		if (editor == null)
			return null;
		final IDocument doc = editor.getDocumentProvider().getDocument(editor.getEditorInput());
		final ISelectionProvider selectionProvider = editor.getSelectionProvider();
		final TextSelection selection = (TextSelection) selectionProvider.getSelection();
		if (selection.isEmpty())
			return null;
		if (selection.getOffset() < 0)
			return null;
		
		final String selectedText = selection.getText();
		String result = null;
		try {
			// final IRegion lineInfo = doc.getLineInformationOfOffset(offset);
			switch(event.getCommand().getId()) {
			case ID_CONVERT_SELECTION_TO_UNICODE:
				result = Unicode.convertToUnicode(selectedText);
				break;
			case ID_CONVERT_SELECTION_TO_ASCII:
				result = Unicode.convertToASCII(selectedText);
				break;
			default:
				Activator.getDefault().logInfo("Unrecognized unicode conversion command.");
				return null;
			}

			doc.replace(selection.getOffset(), selection.getLength(), result);
		} catch (org.eclipse.jface.text.BadLocationException e) {
			Activator.getDefault().logError("Error executing ccommand", e);
			// just do nothing
		}

		return null;
	}

	
	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#isEnabled()
	 */
	@Override
	public boolean isEnabled() {
		final TLAEditor editor = EditorUtil.getTLAEditorWithFocus();
		if (editor == null)
			return false;
		if (((TextSelection) editor.getSelectionProvider().getSelection()).isEmpty())
			return false;
		return super.isEnabled();
	}
}
