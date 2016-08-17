package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.ui.IEditorInput;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2unicode.Unicode;

/**
 * This class is responsible for replacing ASCII TLA special symbols with their Unicode counterparts
 * as you type in the editor.
 * 
 * @author pron
 */
public class TLAUnicodeReplacer {
	private final TLAEditor editor;
	private IDocument doc;
	private Unicode.OnlineReplacer replacer;
	
	public TLAUnicodeReplacer(TLAEditor editor) {
		this.editor = editor;
	}

	public void init(IEditorInput input) {
		this.replacer = new Unicode.OnlineReplacer() {
			@Override
			protected void replace(final int start, final int length, final String u) {
				final IDocument doc0 = doc;
				UIHelper.runUIAsync(new Runnable() {
					public void run() {
						 try {
							  doc0.replace(start, length, u);
						  } catch (BadLocationException e) {
								throw new AssertionError(e);
						  }
					}
				});	
			}
		};
		// editor.getEditorInput()
		
		editor.getDocumentProvider().getDocument(input).addDocumentListener(new IDocumentListener() {
			public void documentChanged(DocumentEvent event) {
				handle(event);				
			}
			
			public void documentAboutToBeChanged(DocumentEvent event) {
			}
		});
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
