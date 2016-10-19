package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.e4.core.services.events.IEventBroker;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentCommand;
import org.eclipse.jface.text.IAutoEditStrategy;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewer;
import org.lamport.tla.toolbox.Activator;

import tla2unicode.Unicode;

/**
 * This class is responsible for replacing ASCII TLA special symbols with their Unicode counterparts
 * as you type in an editor.
 * 
 * @author pron
 */
public class TLAUnicodeReplacer {
	public static final String EVENTID_TOGGLE_UNICODE = "TLA/Unicode/toggle";
	
	// consider using IAutoEditStrategy
	
	public static volatile boolean UNICODE_MODE = true;

	public static String unicode(String text) {
		return UNICODE_MODE ? Unicode.convertToUnicode(text) : text;
	}

//	RightMargin = Activator.getDefault().getPreferenceStore().getInt(
//			EditorPreferencePage.EDITOR_RIGHT_MARGIN);
	
	private Object editor;
	
	private IDocument doc;
	private DocumentCommand command;
	
	private final Unicode.OnlineReplacer replacer;
	
	public static boolean isUnicode() {
		return UNICODE_MODE;
	}
	
	public static void setUnicode(boolean value) {
		if (value == UNICODE_MODE)
			return;
		
		UNICODE_MODE = value;
		
		IEventBroker eventBroker = Activator.getDefault().getWorkbench().getService(IEventBroker.class);
		eventBroker.post(EVENTID_TOGGLE_UNICODE, value);
	}
	
	public static void toggleUnicode() {
		setUnicode(!isUnicode());
	}
	
	private static SourceViewer sourceViewer(Object element) {
		if (element instanceof ISourceViewer)
			return (SourceViewer) element;
		if (element instanceof TLAEditor)
			return sourceViewer(((TLAEditor) element).publicGetSourceViewer());
		return null;
	}
	
	public TLAUnicodeReplacer() {	
		this.replacer = new Unicode.OnlineReplacer() {
			@Override
			protected void replace(int start, int length, String u) {
				 try {
					 if (Unicode.IMMEDIATE_REPLACE.contains(token.toString())) {
						 length--; // the last character isn't displayed
						 overwriteCommand(command, start, length, u, null);
					 } else
						 addCommand(command, start, length, u, null);
					 
					 // fix caret position in a special case
					 if (editor instanceof ISourceViewer) {
						 if (start == 0)
							 ((ISourceViewer) editor).getTextWidget().setCaretOffset(length);
					 }
				  } catch (BadLocationException e) {
						throw new AssertionError(e);
				  }
			}
		};
	}

	public void init(ISourceViewer sourceViewer) {
		this.editor = sourceViewer;
		init0(sourceViewer(sourceViewer));
	}
	
	public void init(TLAEditor editor) {
		this.editor = editor;
		init(sourceViewer(editor));
	}
	
	public void init0(SourceViewer sv) {
		final IAutoEditStrategy strategy = new IAutoEditStrategy() {
			@Override
			public void customizeDocumentCommand(IDocument document, DocumentCommand command) {
				TLAUnicodeReplacer.this.customizeDocumentCommand(document, command);
			}
		};
		
		sv.prependAutoEditStrategy(strategy, IDocument.DEFAULT_CONTENT_TYPE);
		for (String contentType : TLAPartitionScanner.TLA_PARTITION_TYPES)
			sv.prependAutoEditStrategy(strategy, contentType);
		sv.prependAutoEditStrategy(strategy, TLAPartitionScanner.TLA_PCAL);
	}
	
	private void customizeDocumentCommand(IDocument document, DocumentCommand command) {
		this.doc = document;
		this.command = command;
		try {
			if ((command.length == 0 && command.text != null && command.text.length() == 1)
					|| (command.length == 1 && (command.text == null || command.text.isEmpty())))
				handleTyping(command.length, command.offset, command.text);
			else {
				replacer.reset();
				if (command.text != null && !command.text.isEmpty() // ignore deletion
						&& (command.offset != 0 || command.length < doc.getLength())) { // ignore full text replacement
					overwriteCommand(command, command.offset, command.length, Unicode.convertToUnicode(command.text), null);
				}
			}
		} catch (BadLocationException e) {
			throw new AssertionError(e);
	    } finally {
			this.doc = null;
			this.command = null;
		}
	}
	
	private void handleTyping(int length, int offset, String text) {
		// We support only the following cases:
		// 1. The user types a character at the end of the current token.
		// 2. The user types backspace.
		// Any other case (like navigating and typing elsewhere) will reset the token.

//		System.out.println("handle  event: " + event
//				+ " start: " + startOffset + " next: " + nextOffset + " token: \"" + token + "\"");
		if ((replacer.getNextOffset() < 0 || offset == replacer.getNextOffset()) && text.length() == 1)
			replacer.addChar(offset, text.charAt(0));
		else if (length == 1 
				&& text.isEmpty()
				&& offset == replacer.getNextOffset() - 1)
			replacer.backspace();
		else
			replacer.reset();
	}
	
	private static DocumentCommand addCommand(DocumentCommand command, int offset, int length, String text, IDocumentListener owner) throws BadLocationException {
//		if (intersects(command, offset, length))
//			overwriteCommand(command, offset, length, text, owner);
//		else
		command.addCommand(offset, length, text, owner);
		command.caretOffset = offset + text.length() + command.text.length(); //  + length;
		command.doit = false; // why? because!
		return command;
	}
	
	private static DocumentCommand overwriteCommand(DocumentCommand command, int offset, int length, String text, IDocumentListener owner) throws BadLocationException {
		command.offset = offset;
		command.length = length;
		command.text = text;
		command.owner = owner;
		return command;
	}
	
	private static boolean intersects(DocumentCommand command, int offset, int length) {
		// diff middle points if not intersecting
		if (command.offset + command.length <= offset || offset + length <= command.offset)
			return (2 * command.offset + command.length) - (2 * offset + length) == 0;
		return true;
	}
}
