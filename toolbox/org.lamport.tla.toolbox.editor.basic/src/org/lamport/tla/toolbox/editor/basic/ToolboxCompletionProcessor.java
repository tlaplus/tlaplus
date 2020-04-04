/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.editor.basic;

import java.nio.CharBuffer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.SortedMap;
import java.util.TreeMap;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.contentassist.BoldStylerProvider;
import org.eclipse.jface.text.contentassist.ContextInformation;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposalExtension5;
import org.eclipse.jface.text.contentassist.ICompletionProposalExtension7;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.text.contentassist.IContextInformationValidator;
import org.eclipse.jface.viewers.StyledString;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.lamport.tla.toolbox.editor.basic.tla.ITLAReserveredWords;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper;
import org.lamport.tla.toolbox.tool.ToolboxHandle;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.SymbolMatcher;
import tla2sany.semantic.SymbolNode;
import util.UniqueString;

public abstract class ToolboxCompletionProcessor {
	
    protected final SortedMap<String, List<CompletionProposalTemplate>> proposals = new TreeMap<String, List<CompletionProposalTemplate>>();
    
    protected final SymbolMatcher.NameAndTypeMatcher matcher = new SymbolMatcher.NameAndTypeMatcher();
    
	public ICompletionProposal[] computeCompletionProposals(ITextViewer viewer, int offset) {
		final IDocument document = viewer.getDocument();
		// get the selection range
		final Point selectedRange = viewer.getSelectedRange();

		final List<ICompletionProposal> propList = new ArrayList<ICompletionProposal>();
		try {
			// The zero-based row index of the caret.
			final int caretRowIndex = document.getLineOfOffset(offset);
			// The zero-based column index of the caret.
			final int carretColumnIndex = offset - document.getLineOffset(caretRowIndex);
			if (selectedRange.y > 0) {
				// the range is non-empty
				final String text = document.get(selectedRange.x, selectedRange.y);
				computeWordProposals(text, offset, carretColumnIndex, propList);
			} else {
				// the range is empty, no selection in the editor

				// get the region
				final IRegion wordRegion = DocumentHelper.getRegionExpandedBackwards(document, offset,
						DocumentHelper.getDefaultWordDetector());
				final String word = document.get(wordRegion.getOffset(), wordRegion.getLength());
				computeWordProposals(word, offset, carretColumnIndex, propList);
			}
		} catch (final BadLocationException ignore) {
		}
		return propList.toArray(new ICompletionProposal[propList.size()]);
	}

    /**
     * Syntax-based proposal based for word beginning
     */
	private void computeWordProposals(final String word, final int offset, final int carretColumnIndex, final List<ICompletionProposal> propositionList) {
		final int qualifierLength = word.length();
		final int replacementOffset = offset - qualifierLength;

		// keyword and other static proposals
		for (List<CompletionProposalTemplate> list : filterPrefix(proposals, word).values()) {
			// and add to result list
			for (CompletionProposalTemplate template : list) {
				propositionList.add(template.getProposal(replacementOffset, carretColumnIndex - qualifierLength, qualifierLength));
			}
		}
		
		// Try to find matches among the spec's set of symbols (e.g. operators definitions and declarations).
		final SpecObj specObj = ToolboxHandle.getSpecObj();
		if (specObj != null && specObj.getRootModule() != null) { // null if spec hasn't been parsed.
			final ModuleNode rootModule = specObj.getRootModule();

			final Collection<SymbolNode> symbols = rootModule.getSymbols(matcher.setPrefix(word));
			for (final SymbolNode symbolNode : symbols) {
				propositionList.add(new CompletionProposalTemplate(symbolNode.getSignature(), symbolNode.getName(),
						symbolNode.getHumanReadableImage()).getProposal(replacementOffset, carretColumnIndex - qualifierLength, qualifierLength));
			}
		}
	}
    
	public static SortedMap<String, List<CompletionProposalTemplate>> filterPrefix(SortedMap<String, List<CompletionProposalTemplate>> baseMap, String prefix) {
		if (prefix.length() > 0) {
			final char nextLetter = (char) (prefix.charAt(prefix.length() - 1) + 1);
 			final String end = prefix.substring(0, prefix.length() - 1) + nextLetter;
			return baseMap.subMap(prefix, end);
		}
		return baseMap;
	}

	public IContextInformation[] computeContextInformation(ITextViewer viewer, int offset) {
		// Retrieve selected range
		final Point selectedRange = viewer.getSelectedRange();
		if (selectedRange.y > 0) {
			// Text is selected. Create a context information array.
			final IContextInformation[] contextInfos = new ContextInformation[ITLAReserveredWords.ALL_WORDS_ARRAY.length];

			// Create one context information item for each style
			for (int i = 0; i < ITLAReserveredWords.ALL_WORDS_ARRAY.length; i++) {
				contextInfos[i] = new ContextInformation(null, ITLAReserveredWords.ALL_WORDS_ARRAY[i] + " Style");
			}
			return contextInfos;
		}
		return new ContextInformation[0];
	}

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getCompletionProposalAutoActivationCharacters()
     */
	public char[] getCompletionProposalAutoActivationCharacters() {
		return null;
	}

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getContextInformationAutoActivationCharacters()
     */
	public char[] getContextInformationAutoActivationCharacters() {
		return null;
	}

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getContextInformationValidator()
     */
	public IContextInformationValidator getContextInformationValidator() {
		return null;
	}

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getErrorMessage()
     */
	public String getErrorMessage() {
		return null;
	}
	
	protected static class CompletionProposalTemplate {
		private final String fReplacementString;
		private final Image fImage;
		private final IContextInformation fContextInformation;
		private final String fAdditionalProposalInfo;
		private final String fDisplayString;
		
		public CompletionProposalTemplate(String replacementString, Image image, String dipslayString,
				IContextInformation contextInformation, String additionalProposalInfo) {
			this.fReplacementString = replacementString;
			this.fImage = image;
			this.fDisplayString = dipslayString;
			this.fContextInformation = contextInformation;
			this.fAdditionalProposalInfo = additionalProposalInfo;
		}
		
		public CompletionProposalTemplate(String replacementString, Image image, String dipslayString,
				String additionalProposalInfo) {
			this.fReplacementString = replacementString;
			this.fImage = image;
			this.fDisplayString = dipslayString;
			this.fContextInformation = null;
			this.fAdditionalProposalInfo = additionalProposalInfo;
		}
		
		public CompletionProposalTemplate(UniqueString replacementString, UniqueString dipslayString,
				String additionalProposalInfo) {
			this(replacementString.toString(), dipslayString.toString(), additionalProposalInfo);
		}
		
		public CompletionProposalTemplate(String replacementString, UniqueString dipslayString,
				String additionalProposalInfo) {
			this(replacementString, dipslayString.toString(), additionalProposalInfo);
		}
		
		public CompletionProposalTemplate(String replacementString, String dipslayString,
				String additionalProposalInfo) {
			this.fReplacementString = replacementString;
			this.fImage = null;
			this.fDisplayString = dipslayString;
			this.fContextInformation = null;
			this.fAdditionalProposalInfo = additionalProposalInfo;
		}
		
		public CompletionProposalTemplate(String replacementString) {
			this.fReplacementString = replacementString;
			this.fImage = null; // Image for keywords?!
			this.fContextInformation = null;
			this.fAdditionalProposalInfo = null;
			this.fDisplayString = null;
		}

		public ICompletionProposal getProposal(final int replacementOffset, final int wordStartColumnIndex, final int qualifierLength) {
			final String indent = CharBuffer.allocate(wordStartColumnIndex).toString().replace( '\0', ' ' );
			final String indentedReplacementString = fReplacementString.replace("\n", "\n" + indent);
			return new ToolboxCompletionProposal(indentedReplacementString, replacementOffset, qualifierLength,
					indentedReplacementString.length(), fImage, fDisplayString, fContextInformation,
					fAdditionalProposalInfo);
		}
	}
	
	public static class ToolboxCompletionProposal implements ICompletionProposal, ICompletionProposalExtension5, ICompletionProposalExtension7 {

		/** The string to be displayed in the completion proposal popup. */
		private String fDisplayString;
		/** The replacement string. */
		private String fReplacementString;
		/** The replacement offset. */
		private int fReplacementOffset;
		/** The replacement length. */
		private int fReplacementLength;
		/** The cursor position after this proposal has been applied. */
		private int fCursorPosition;
		/** The image to be displayed in the completion proposal popup. */
		private Image fImage;
		/** The context information of this proposal. */
		private IContextInformation fContextInformation;
		/** The additional info of this proposal. */
		private String fAdditionalProposalInfo;

		/**
		 * Creates a new completion proposal based on the provided information. The
		 * replacement string is considered being the display string too. All remaining
		 * fields are set to <code>null</code>.
		 *
		 * @param replacementString
		 *            the actual string to be inserted into the document
		 * @param replacementOffset
		 *            the offset of the text to be replaced
		 * @param replacementLength
		 *            the length of the text to be replaced
		 * @param cursorPosition
		 *            the position of the cursor following the insert relative to
		 *            replacementOffset
		 */
		public ToolboxCompletionProposal(String replacementString, int replacementOffset, int replacementLength,
				int cursorPosition) {
			this(replacementString, replacementOffset, replacementLength, cursorPosition, null, null, null, null);
		}

		/**
		 * Creates a new completion proposal. All fields are initialized based on the
		 * provided information.
		 *
		 * @param replacementString
		 *            the actual string to be inserted into the document
		 * @param replacementOffset
		 *            the offset of the text to be replaced
		 * @param replacementLength
		 *            the length of the text to be replaced
		 * @param cursorPosition
		 *            the position of the cursor following the insert relative to
		 *            replacementOffset
		 * @param image
		 *            the image to display for this proposal
		 * @param displayString
		 *            the string to be displayed for the proposal
		 * @param contextInformation
		 *            the context information associated with this proposal
		 * @param additionalProposalInfo
		 *            the additional information associated with this proposal
		 */
		public ToolboxCompletionProposal(String replacementString, int replacementOffset, int replacementLength,
				int cursorPosition, Image image, String displayString, IContextInformation contextInformation,
				String additionalProposalInfo) {
			Assert.isNotNull(replacementString);
			Assert.isTrue(replacementOffset >= 0);
			Assert.isTrue(replacementLength >= 0);
			Assert.isTrue(cursorPosition >= 0);

			fReplacementString = replacementString;
			fReplacementOffset = replacementOffset;
			fReplacementLength = replacementLength;
			fCursorPosition = cursorPosition;
			fImage = image;
			fDisplayString = displayString;
			fContextInformation = contextInformation;
			fAdditionalProposalInfo = additionalProposalInfo;
		}

		public void apply(IDocument document) {
			try {
				document.replace(fReplacementOffset, fReplacementLength, fReplacementString);
			} catch (BadLocationException x) {
				// ignore
			}
		}

		public Point getSelection(IDocument document) {
			return new Point(fReplacementOffset + fCursorPosition, 0);
		}

		public IContextInformation getContextInformation() {
			return fContextInformation;
		}

		public Image getImage() {
			return fImage;
		}

		public String getDisplayString() {
			if (fDisplayString != null)
				return fDisplayString;
			return fReplacementString;
		}

		public String getAdditionalProposalInfo() {
			return fAdditionalProposalInfo;
		}

		public Object getAdditionalProposalInfo(IProgressMonitor monitor) {
			return getAdditionalProposalInfo();
		}

		public StyledString getStyledDisplayString(IDocument document, int offset,
				BoldStylerProvider boldStylerProvider) {
			final StyledString styledString = new StyledString();
			styledString.append(getDisplayString());
			styledString.append(": ");
			styledString.append(fReplacementString.replaceAll("\n[ ]*", " "), StyledString.COUNTER_STYLER);
			return styledString;
		}
	}
}
