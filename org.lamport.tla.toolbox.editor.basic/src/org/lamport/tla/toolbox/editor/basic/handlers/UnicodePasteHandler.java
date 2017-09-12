package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.swt.dnd.Clipboard;
import org.eclipse.swt.dnd.TextTransfer;
import org.eclipse.swt.dnd.Transfer;
import org.eclipse.swt.dnd.TransferData;
import org.eclipse.swt.widgets.Display;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;

import tla2unicode.Unicode;

/**
 * This is the handler method for the following commands:
 * 
 * Paste as Unicode
 * 
 * @author pron
 * 
 */
public class UnicodePasteHandler extends AbstractHandler implements IHandler {
	/*
	 * Command ids.
	 */
	public static final String ID_PASTE_AS_UNICODE = "org.lamport.tla.toolbox.editor.basic.pasteAsUnicode";

//	private final Clipboard cb;
//	
//	public UnicodePasteHandler() {
//		this.cb = new Clipboard(null);
//	}
//	
//	@Override
//	public void dispose() {
//		cb.dispose();
//		super.dispose();
//	}
	
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
		
		final String text;

		final TextTransfer transfer = TextTransfer.getInstance();
		Clipboard cb = new Clipboard(null);
		try {
			text = (String)cb.getContents(transfer);
		} finally {
			cb.dispose();
		}
		
		if (text == null || text.isEmpty())
			return null;
		
		String result = Unicode.convertToUnicode(text);
		try {
			doc.replace(selection.getOffset(), selection.getLength(), result);
			selectionProvider.setSelection(new TextSelection(selection.getOffset() + result.length(), 0));
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
		
		boolean enabled = false;		
		Clipboard cb = new Clipboard(null);
		try {
			final TransferData[] available= cb.getAvailableTypes();
			for (int i = 0; i < available.length; i++) {
				if (TextTransfer.getInstance().isSupportedType(available[i])) {
					enabled = true;
					break;
				}
			}
		} finally {
			cb.dispose();
		}
		if (!enabled)
			return false;
		return super.isEnabled();
	}
}
