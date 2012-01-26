/**
 * 
 */
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

/**
 * This is the handler method for the following commands:
 * 
 * Start Boxed Comment 
 * 
 * Format Comment Box 
 * 
 * Comment Format and 
 * 
 * Box Comment 
 * 
 * Unbox Comment
 * 
 * I put them all in the same handler to make it simpler to implement. It would
 * be more Eclipsically correct to put Start Boxed Comment and Unbox Comment in
 * separate handlers. For one thing, the commands could be disabled when they're
 * not applicable instead of their just doing nothing. Also, to avoid either
 * recomputing values or having methods that take lots of arguments, the code
 * passes values between methods by setting private fields. It would be more
 * elegant to create a new class of object in which those values are passed.
 * 
 * @author lamport
 * 
 */
/**
 * @author lamport
 * 
 */
public class BoxedCommentHandler extends AbstractHandler implements IHandler {
	/*
	 * The following is set to the preference value.
	 */
	private int RightMargin;

	/*
	 * The following private fields are used only for sharing information
	 * between methods during a single call to the execute method. The first
	 * batch are set by execute before calling the methods that execute the
	 * particular commands.
	 */
	private IDocument doc; // The document being edited.
	private String text; // The document as a string.
	private ISelectionProvider selectionProvider; // 
	private TextSelection selection; // The current selection.
	private int offset; // The current offset.
	private IRegion lineInfo; // The lineInfo for the current offset.

	/*
	 * The following fields are for holding information about boxed comments
	 * being constructed.
	 */
	int margin; // the value used for the right margin
	int indent; // the offset from the beginning of its line to the starting
	// `(*'
	int beginCommentOffset;
	int endCommentOffset; // the offset immediately FOLLOWING '*)' ending the
	// comment.

	/*
	 * The following are the command ids.
	 */
	public final String startBoxedCommentId = "org.lamport.tla.toolbox.editor.basic.startBoxedComment";
	public final String boxCommentId = "org.lamport.tla.toolbox.editor.basic.boxComment";
	public final String unboxCommentId = "org.lamport.tla.toolbox.editor.basic.unboxComment";
	public final String formatCommentId = "org.lamport.tla.toolbox.editor.basic.formatComment";
	public final String formatAndBoxCommentId = "org.lamport.tla.toolbox.editor.basic.formatAndBoxComment";

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.
	 * ExecutionEvent)
	 */
	public Object execute(ExecutionEvent event) throws ExecutionException {
		TLAEditor editor;
		editor = EditorUtil.getTLAEditorWithFocus();
		// gets the editor to which command applies
		if (editor == null) {
			return null;
		}

		doc = editor.getDocumentProvider().getDocument(editor.getEditorInput());
		text = doc.get();
		selectionProvider = editor.getSelectionProvider();
		selection = (TextSelection) selectionProvider.getSelection();
		offset = selection.getOffset();

		RightMargin = Activator.getDefault().getPreferenceStore().getInt(
				EditorPreferencePage.EDITOR_RIGHT_MARGIN);
		if (offset < 0) {
			return null;
		}
		try {
			lineInfo = doc.getLineInformationOfOffset(offset);

			String cmd = event.getCommand().getId();

			if (cmd.equals(startBoxedCommentId)) {
				startBoxedComment();
			} else if (cmd.equals(boxCommentId)) {
				boxComment();
			} else if (cmd.equals(formatAndBoxCommentId)) {
				formatAndBoxComment();
			} else if (cmd.equals(unboxCommentId)) {
				unboxComment();
			} else if (cmd.equals(formatCommentId)) {
				formatComment();
			} else {
				Activator.logInfo("Unrecognized boxing command.");
			}

		} catch (org.eclipse.jface.text.BadLocationException e) {
			Activator.logError("Error executing comment-boxing command", e);
			// just do nothing
		}

		// free the space. (Probably not worth doing.)
		doc = null;
		text = null;
		selectionProvider = null;
		selection = null;
		lineInfo = null;

		return null;
	}

	/*
	 * Replaces the selected region with (or puts at the cursor if no region is
	 * selected): - A "(****..." - two new-line characters, - a series of spaces
	 * followed by spaces and a "...******)", with spaces so they line up.
	 * 
	 * Modified by LL on 15 Sep 2011 so it adds a blank line after
	 * the ****) iff there is a non-space character between the cursor and
	 * the end of the line.
	 */
	private void startBoxedComment()
			throws org.eclipse.jface.text.BadLocationException {
		int indent = offset - lineInfo.getOffset() + 1;

		// set dontAddNewLine to true iff the rest of the line, starting from offset
		// consists entirely of // space characters.
		int restOfLineLength = lineInfo.getOffset() -  offset + lineInfo.getLength();
		String restOfLine = doc.get(offset, restOfLineLength);
		boolean dontAddNewLine = StringHelper.onlySpaces(restOfLine);

		String asterisks = StringHelper.copyString("*", Math.max(3, RightMargin
				- indent - 1));
		String newText = "(" + asterisks + StringHelper.newline
				+ StringHelper.newline + StringHelper.copyString(" ", indent)
				+ asterisks + ")" + (dontAddNewLine ? "" : StringHelper.newline);
		doc.replace(selection.getOffset(), selection.getLength(), newText);
		selectionProvider.setSelection(new TextSelection(offset + 1
				+ asterisks.length() + StringHelper.newline.length(), 0));
	}

	private void formatAndBoxComment()
			throws org.eclipse.jface.text.BadLocationException {
		if (formatComment()) {
			// Need to recompute things that were changed by executing
			// formatComment.
			text = doc.get();
			selection = (TextSelection) selectionProvider.getSelection();
			offset = selection.getOffset();

			boxComment();
		}
		return;
	}

	/*
	 * Puts the asterisk box around the current (* ... *) comment that would be
	 * produced by the following algorithm:
	 * 
	 * - Any non-white-space text following the (*..* on the same line is put on
	 * a new line with no beginning white space.
	 * 
	 * - If there is any non-white-space text preceding the *...*), then the
	 * *...*) is moved to a new line.
	 * 
	 * - If there is any non-white-space following the *...*), then a new line
	 * is begun immediately after the *...*) token.
	 * 
	 * - The (*...* token is replaced by a (*....*) starting at the same
	 * position and going to the maximum of the right margin and the starting
	 * position + 4 (for a minimun length starting string of (**)).
	 * 
	 * - The *...*) token is replaced by a (*....*) token the same width as and
	 * starting at the same column as the opening one.
	 * 
	 * - Each line between the two (*...*) lines is preceded by spaces + (* +
	 * one space so the (* is aligned with the starting (*...*) token and has
	 * white space added or removed and *) added so that the *) is as far to the
	 * left as possible so it (a) is preceded by at least one space and (b) is
	 * not to the left of the *) of the starting (*...*) token. Returns false
	 * iff it detects an error.
	 */
	private boolean boxComment()
			throws org.eclipse.jface.text.BadLocationException {
		// set begin/endCommentOffset

		int beginCommentLength; // the offset of the '(' of the '(*' starting
		// the comment.
		// IRegion beginCommentLineInfo;
		// IRegion endCommentLineInfo;
		int endCommentLength;
		// int firstLineOffset = -1; // if there's an extra line after the
		// '(*...*'
		// int firstLineLength = 0; // then these are its length & offset, else
		// offset = -1
		// int lastLineOffset = -1; // if there's an extra line after the
		// '(*...*'
		// int lastLineLength = 0; // then these are its length & offset, else
		// offset = -1

		// set margin

		setCommentFields();

		if ((beginCommentOffset < 0) || (endCommentOffset < 2)) {
			return false; // error: not inside comment
		}

		// set beginCommentLength
		beginCommentLength = 2;
		while (text.charAt(beginCommentOffset + beginCommentLength) == '*') {
			beginCommentLength++;
		}

		// set endCommentLineInfo, endCommentLength
		// endCommentLineInfo =
		// doc.getLineInformationOfOffset(endCommentOffset);
		endCommentLength = 2;
		while (text.charAt(endCommentOffset - 1 - endCommentLength) == '*') {
			endCommentLength++;
		}

		int beginLine = doc.getLineOfOffset(beginCommentOffset);
		int endLine = doc.getLineOfOffset(endCommentOffset);

		StringBuffer buffer = new StringBuffer(4 * margin);
		buffer.append(makeCommentBoxStart());
		buffer.append(StringHelper.newline);

		// Handle special case of entire comment on one line.
		if (beginLine == endLine) {
			String singleLine = doc.get(
					beginCommentOffset + beginCommentLength, endCommentOffset
							- (beginCommentOffset + beginCommentLength)
							- endCommentLength);
			buffer
					.append(makeCommentBoxLine(StringHelper
							.trimFront(singleLine)));
			buffer.append(StringHelper.newline);
		} else {

			// Produce a first line for anything after the (* on its line.
			String restOfLine = doc.get(
					beginCommentOffset + beginCommentLength, doc
							.getLineOffset(beginLine)
							+ doc.getLineLength(beginLine)
							- (beginCommentOffset + beginCommentLength));
			if (!StringHelper.onlySpaces(restOfLine)) {
				buffer.append(makeCommentBoxLine(StringHelper
						.trimFront(restOfLine)));
				buffer.append(StringHelper.newline);
			}

			for (int i = beginLine + 1; i < endLine; i++) {
				buffer.append(makeCommentBoxLine(doc.get(doc.getLineOffset(i),
						doc.getLineLength(i))));
				buffer.append(StringHelper.newline);
			}

			// Produce a last line for anything before the *) on its line.
			int lineOffset = doc.getLineOffset(endLine);
			String startOfLine = doc.get(lineOffset, endCommentOffset
					- endCommentLength - lineOffset);
			if (!StringHelper.onlySpaces(startOfLine)) {
				buffer.append(makeCommentBoxLine(startOfLine));
				buffer.append(StringHelper.newline);
			}
		}

		buffer.append(makeCommentBoxEnd());

		// If there is text following the ending *) on the same line,
		// append a StringHelper.newline to the output.
		if (!StringHelper.onlySpaces(doc.get(endCommentOffset, doc
				.getLineOffset(endLine)
				- endCommentOffset + doc.getLineLength(endLine)))) {
			buffer.append(StringHelper.newline);
		}

		doc.replace(beginCommentOffset, endCommentOffset - beginCommentOffset,
				buffer.toString());

		return true;
	}

	/*
	 * Removes the box from a comment in the obvious way so that boxing it
	 * should produce the same result. However, anything outside the box but on
	 * the same line as the box will be deleted, except for text preceding the
	 * first line of the box or following the last line.
	 */
	private final void unboxComment()
			throws org.eclipse.jface.text.BadLocationException {
		// Check if the cursor is right before ')', or right before '*)',
		// and modify offset to put it before '**)'.
		if ((offset > 2) && (text.charAt(offset) == ')')) {
			offset--;
		}
		if ((offset > 1) && (text.charAt(offset) == '*')) {
			offset--;
		}
		String errorMsg = "Unbox Coment command called when not inside a boxed comment.";
		int startOffset = text.lastIndexOf("(**", offset);
		int endOffset = text.indexOf("**)", offset) + 3;
		if ((startOffset < 0) || (endOffset < 0)) {
			displayNotInBoxedCommentError(errorMsg);
			return;
		}

		int startIndent = startOffset
				- doc.getLineOffset(doc.getLineOfOffset(startOffset));
		int asteriskLength = RightMargin - startIndent - 1;
		String asterisks = StringHelper.copyString("*", asteriskLength);

		int beginLine = doc.getLineOfOffset(startOffset);
		int endLine = doc.getLineOfOffset(endOffset);

		if (beginLine == endLine) {
			if (text.substring(startOffset + 1, endOffset - 1).equals(
					StringHelper.copyString("*", endOffset - startOffset - 2))) {
				displayNotInBoxedCommentError("You are at the beginning or ending line of a boxed comment,\n"
						+ "not inside the boxed comment");
			} else {
				displayNotInBoxedCommentError(errorMsg);
			}
			return;
		}

		// we need to compute the indent of the final *);
		// We compute how big a StringBuffer is needed. If the command is
		// issued outside a boxed comment, this value can be zero.
		// In that case, we ignore the value and let some later test
		// or exception figure out what to do.
		StringBuffer buffer = null;
		int bufferSize = endOffset - startOffset - 6 * (endLine - beginLine);
		if (bufferSize > 0) {
			buffer = new StringBuffer(bufferSize);
		} else {
			buffer = new StringBuffer();
		}
		// We replace everything from the starting (
		// and the ending ) . We must therefore begin
		// with asterisks and a StringHelper.newline;
		buffer.append(asterisks);
		buffer.append(StringHelper.newline);

		// process the individual lines.
		for (int i = beginLine + 1; i < endLine; i++) {
			IRegion lineInfo = doc.getLineInformation(i);
			String currentLine = doc.get(lineInfo.getOffset(), lineInfo
					.getLength());
			int beginTokenIndex = currentLine.indexOf("(*");
			int endTokenIndex = currentLine.indexOf("*)");
			if ((!(beginTokenIndex < 0))
					&& (!(beginTokenIndex > endTokenIndex))) {
				buffer.append(StringHelper.trimEnd(currentLine.substring(
						beginTokenIndex + 3, endTokenIndex)));
				buffer.append(StringHelper.newline);
			} else {
				buffer.append(currentLine);
				buffer.append(StringHelper.newline);
			}

		}
		buffer.append(StringHelper.copyString(" ", startIndent));
		buffer.append(asterisks);
		doc.replace(startOffset + 1, endOffset - 2 - startOffset, buffer
				.toString());
		return;

	}

	void displayNotInBoxedCommentError(String msg) {
		Shell shell = UIHelper.getShellProvider().getShell();
		MessageDialog.openError(shell, "Not inside a boxed comment", msg);
		return;
	}

	/*
	 * Formats comments for boxing. It just formats the lines after the line
	 * containing the starting (* and before the line containing the ending *).
	 * A line beginning with a space character is left unchanged. A sequence of
	 * lines beginning with non-space characters are considered to be a single
	 * paragraph and are formatted as such for boxing.
	 * 
	 * Returns false iff it detects an error.
	 */
	private final boolean formatComment()
			throws org.eclipse.jface.text.BadLocationException {
		setCommentFields();

		int beginCommentLine = doc.getLineOfOffset(beginCommentOffset);
		int endCommentLine = doc.getLineOfOffset(endCommentOffset);

		// Return if there are no lines between the begin and end
		// comments.
		if (endCommentLine - beginCommentLine < 2) {
			return false; // error, no lines between begin and end
		}

		// the following parameters are the offsets of the text to
		// be replaced
		int beginReplacementOffset = doc.getLineOffset(beginCommentLine + 1);
		int endReplacementOffset = doc.getLineOffset(endCommentLine);

		// buffer is the replacement text accumulated thus far.
		StringBuffer buffer = new StringBuffer(
				50 * (endCommentLine - beginCommentLine));

		// lineWidth is the maximum number of characters that can fit
		// in one line of a paragraph.
		int lineWidth = margin - indent - 6;
		// unfinishedLineWidth is the number of characters in an
		// incomplete paragraph at the end of buffer.
		int unfinishedLineWidth = 0;

		// parText is an array of paragraph words, where elements in positions
		// nextWord .. parText.length - 1 have not yet been added to buffer.
		for (int i = beginCommentLine + 1; i < endCommentLine; i++) {
			IRegion lineInfo = doc.getLineInformation(i);
			String currentLine = doc.get(lineInfo.getOffset(), lineInfo
					.getLength());
			if ((currentLine.length() == 0)
					|| (Character.isSpaceChar(currentLine.charAt(0)))) {
				// This line is not part of a paragraph.
				// Output a StringHelper.newline if there's an unfinished
				// paragraph.
				if (unfinishedLineWidth > 0) {
					buffer.append(StringHelper.newline);
					unfinishedLineWidth = 0;
				}
				// Output the line and an endline
				buffer.append(currentLine);
				buffer.append(StringHelper.newline);
			} else {
				// This line is part of a paragraph. Set the array words
				// to the words on this line.
				String[] words = StringHelper.getWords(currentLine);

				// Add all the words on the line to the buffer.
				for (int nextPos = 0; nextPos < words.length; nextPos++) {
					String nextWord = words[nextPos];
					if (unfinishedLineWidth == 0) {
						// It's the first word on an output line, so just put it
						// in the buffer.
						buffer.append(nextWord);
						unfinishedLineWidth = nextWord.length();
					} else {
						// It's not the first word on the output line, so must
						// add it to the current line iff it fits, else must
						// start a new line.
						boolean followsPeriod = (buffer
								.charAt(buffer.length() - 1) == '.');
						int nextWidth = unfinishedLineWidth
								+ (followsPeriod ? 2 : 1) + nextWord.length();
						if (nextWidth > lineWidth) {
							buffer.append(StringHelper.newline);
							buffer.append(nextWord);
							unfinishedLineWidth = nextWord.length();
						} else {
							buffer.append(followsPeriod ? "  " : " ");
							buffer.append(nextWord);
							unfinishedLineWidth = nextWidth;
						}
					}
				}

			}
		} // end for
		// Output a newline if there's an unfinished paragraph.
		if (unfinishedLineWidth > 0) {
			buffer.append(StringHelper.newline);
			unfinishedLineWidth = 0;
		}
		doc.replace(beginReplacementOffset, endReplacementOffset
				- beginReplacementOffset, buffer.toString());

		return true;

	}

	/**
	 * Sets beginCommentOffset, endCommentOffset, indent, and margin
	 * 
	 * @throws org.eclipse.jface.text.BadLocationException
	 */
	private void setCommentFields()
			throws org.eclipse.jface.text.BadLocationException {
		// Following code modified by LL on 13 Apr 2011 so that it
		// finds the correct beginning and end of the comment if
		// if the cursor is at right after the "(" or right before
		// the ")" that bracket the comment.
		int searchOffset = offset;
		if ((offset > 0) && text.charAt(offset - 1) == '(') {
			searchOffset++;
		}
		beginCommentOffset = text.lastIndexOf("(*", searchOffset);
		searchOffset = offset;
		if (text.charAt(offset) == ')') {
			searchOffset--;
		}
		endCommentOffset = text.indexOf("*)", searchOffset) + 2;

		IRegion beginCommentLineInfo = doc
				.getLineInformationOfOffset(beginCommentOffset);
		indent = beginCommentOffset - beginCommentLineInfo.getOffset();

		margin = Math.max(RightMargin, indent + 4);
	}

	/*
	 * Returns the box's ending (******) line, with no newline at end.
	 */
	private final String makeCommentBoxEnd() {
		return StringHelper.copyString(" ", indent) + "(*"
				+ StringHelper.copyString("*", margin - indent - 4) + "*)";
	}

	/*
	 * Returns the box's starting (******) line, with no spaces at the beginning
	 * and no newline at end.
	 */
	private final String makeCommentBoxStart() {
		return "(*" + StringHelper.copyString("*", margin - indent - 4) + "*)";
	}

	/*
	 * For a line str, returns the (* str *) box line, with no newline at end.
	 */
	private final String makeCommentBoxLine(String str) {
		String trimmed = StringHelper.trimEnd(str);
		int endSpaces = Math.max(0, margin - trimmed.length() - indent - 6);
		return StringHelper.copyString(" ", indent) + "(* " + trimmed
				+ StringHelper.copyString(" ", endSpaces) + " *)";
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#isEnabled()
	 */
	@Override
	public boolean isEnabled() {
		if (EditorUtil.getTLAEditorWithFocus() == null) {
			return false;
		}
		return super.isEnabled();
	}
}
