package org.lamport.tla.toolbox.editor.basic.tla;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.contentassist.ContextInformation;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.swt.graphics.Point;
import org.lamport.tla.toolbox.editor.basic.ToolboxCompletionProcessor;
import org.lamport.tla.toolbox.editor.basic.pcal.IPCalReservedWords;

/**
 * Syntactic auto-completion processor
 * @author Simon Zambrovski
 */
public class TLACompletionProcessor extends ToolboxCompletionProcessor implements IContentAssistProcessor
{
    public TLACompletionProcessor() {
    	final List<String> asList = Arrays.asList(ITLAReserveredWords.ALL_WORDS_ARRAY);
    	for (String string : asList) {
    		final List<CompletionProposalTemplate> proposal = new ArrayList<CompletionProposalTemplate>(1);
    		proposal.add(new CompletionProposalTemplate(string + " "));
			proposals.put(string, proposal);
		}
    	
		// Define PCal "algorithm" here because the PCalCompletionProcessor is only
		// active inside an algorithm definition (chicken or egg problem).
		final List<CompletionProposalTemplate> l = new ArrayList<CompletionProposalTemplate>(1);
		l.add(new CompletionProposalTemplate(
				"(***************************************************************************\r\n"
						+ "--algorithm AlgorithmName {\r\n}\r\n"
						+ "***************************************************************************)\r\n",
				IPCalReservedWords.ALGORITHM, IPCalReservedWords.ALGORITHM_HELP));
		proposals.put(ITLAReserveredWords.ALGORITHM, l);
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#computeContextInformation(org.eclipse.jface.text.ITextViewer, int)
     */
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
}
