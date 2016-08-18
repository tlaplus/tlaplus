package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.ITextInputListener;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.editors.text.TextEditor;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2unicode.Unicode;

/**
 * This class is responsible for replacing ASCII TLA special symbols with their Unicode counterparts
 * as you type in an editor.
 * 
 * @author pron
 */
public class TLAUnicodeReplacer {
	public static volatile boolean UNICODE_MODE = true;
	
//	RightMargin = Activator.getDefault().getPreferenceStore().getInt(
//			EditorPreferencePage.EDITOR_RIGHT_MARGIN);
	
	private Object editor;
	private IDocument doc;
	private final Unicode.OnlineReplacer replacer;
	private final IDocumentListener listener = new IDocumentListener() {
		public void documentChanged(DocumentEvent event) {
			if (UNICODE_MODE)
				handle(event);				
		}
		
		public void documentAboutToBeChanged(DocumentEvent event) {
		}
	};
	
	public TLAUnicodeReplacer() {	
		this.replacer = new Unicode.OnlineReplacer() {
			@Override
			protected void replace(final int start, final int length, final String u) {
				final IDocument doc0 = doc;
				final Object ed = editor;
				UIHelper.runUIAsync(new Runnable() {
					public void run() {
						 try {
							 doc0.replace(start, length, u);
							 
							 // fix caret position in a special case
							 if (ed instanceof ISourceViewer) {
								 if (start == 0)
									 ((ISourceViewer) ed).getTextWidget().setCaretOffset(length);
							 }
						  } catch (BadLocationException e) {
								throw new AssertionError(e);
						  }
					}
				});
			}
		};
	}

	public void init(ISourceViewer editor) {
		this.editor = editor;
		editor.addTextInputListener(new ITextInputListener() {
			public void inputDocumentChanged(IDocument oldInput, IDocument newInput) {
				if (oldInput != null)
					oldInput.removeDocumentListener(listener);
				init(newInput);
			}
			
			public void inputDocumentAboutToBeChanged(IDocument oldInput, IDocument newInput) {
			}
		});
		init(editor.getDocument());
	}
	
	public void init(TextEditor editor) {
		final IEditorInput input = editor.getEditorInput();
		init(editor.getDocumentProvider().getDocument(input));
	}
	
	public void init(IDocument document) {
		if (document != null)
			document.addDocumentListener(listener);
	}
	
	private void handle(DocumentEvent event) {
		// As the user types, if we think we may be in an interesting token,
		// we collect characters into `token'.
		
		if (doc != null)
			return; // recursive
		doc = event.getDocument();
		try {
			// We support only the following cases:
			// 1. The user types a character at the end of the current token.
			// 2. The user types backspace.
			// Any other case (like navigating and typing elsewhere) will reset the token.

//			System.out.println("handle  event: " + event
//					+ " start: " + startOffset + " next: " + nextOffset + " token: \"" + token + "\"");
			if (event.getLength() == 0 
				&& (replacer.getNextOffset() < 0 || event.getOffset() == replacer.getNextOffset())
				&& event.getText().length() == 1)
				replacer.addChar(event.getOffset(), event.getText().charAt(0));
			else if (event.getLength() == 1 
					&& event.getText().isEmpty()
					&& event.getOffset() == replacer.getNextOffset() - 1)
				replacer.backspace();
			else
				replacer.reset();
		} finally {
			doc = null;
		}
	}
}
