package org.lamport.tla.toolbox.editor.basic.tla;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ContextInformation;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.text.contentassist.IContextInformationValidator;
import org.eclipse.swt.graphics.Point;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper;

/**
 * Syntactic auto-completion processor
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLACompletionProcessor implements IContentAssistProcessor
{
    private String[] proposals = ITLAReserveredWords.ALL_WORDS_ARRAY;

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#computeCompletionProposals(org.eclipse.jface.text.ITextViewer, int)
     */
    public ICompletionProposal[] computeCompletionProposals(ITextViewer viewer, int offset)
    {
        /*
        // show all proposals without checking the context
        ICompletionProposal[] result = new ICompletionProposal[fgProposals.length];
        for (int i = 0; i < fgProposals.length; i++)
        {
            IContextInformation info = new ContextInformation(fgProposals[i], "");
            result[i] = new CompletionProposal(fgProposals[i], offset, 0, fgProposals[i].length(), null,
                    fgProposals[i], info, "");
        }
        return result;
        */

        IDocument document = viewer.getDocument();
        // get the selection range
        Point selectedRange = viewer.getSelectedRange();

        List propList = new ArrayList();
        try
        {
            if (selectedRange.y > 0)
            {
                // the range is non-empty
                String text = document.get(selectedRange.x, selectedRange.y);
                computeWordProposals(text, offset, propList);
            } else
            {
                // the range is empty, no selection in the editor

                // get the region
                IRegion wordRegion = DocumentHelper.getRegionExpandedBackwards(document, offset, DocumentHelper
                        .getDefaultWordDetector());
                String word = document.get(wordRegion.getOffset(), wordRegion.getLength());
                System.out.println("Content assist for '" + word + "'" + wordRegion );
                computeWordProposals(word, offset, propList);
            }
        } catch (BadLocationException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        ICompletionProposal[] proposals = new ICompletionProposal[propList.size()];
        propList.toArray(proposals);

        return proposals;

    }

    /**
     * Syntax-based proposal based for word beginning
     * @param word
     * @param offset
     * @param propositionList
     */
    private void computeWordProposals(String word, int offset, List propositionList)
    {
        int qualifierLength = word.length();

        // Loop through all proposals
        for (int i = 0; i < proposals.length; i++)
        {
            String proposalText = proposals[i];

            // Check if proposal matches qualifier
            if (proposalText.startsWith(word))
            {
                // compute whole proposal text
                String text = proposalText + " ";

                // Derive cursor position
                int cursor = proposalText.length();

                // Construct proposal
                CompletionProposal proposal = new CompletionProposal(text, offset - qualifierLength, qualifierLength,
                        cursor);

                // and add to result list
                propositionList.add(proposal);
            }
        }

    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#computeContextInformation(org.eclipse.jface.text.ITextViewer, int)
     */
    public IContextInformation[] computeContextInformation(ITextViewer viewer, int offset)
    {
        // Retrieve selected range
        Point selectedRange = viewer.getSelectedRange();
        if (selectedRange.y > 0)
        {
            // Text is selected. Create a context information array.
            ContextInformation[] contextInfos = new ContextInformation[ITLAReserveredWords.ALL_WORDS_ARRAY.length];

            // Create one context information item for each style
            for (int i = 0; i < ITLAReserveredWords.ALL_WORDS_ARRAY.length; i++)
                contextInfos[i] = new ContextInformation(null, ITLAReserveredWords.ALL_WORDS_ARRAY[i] + " Style");
            return contextInfos;
        }
        return new ContextInformation[0];
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getCompletionProposalAutoActivationCharacters()
     */
    public char[] getCompletionProposalAutoActivationCharacters()
    {
        return null;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getContextInformationAutoActivationCharacters()
     */
    public char[] getContextInformationAutoActivationCharacters()
    {
        return null;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getContextInformationValidator()
     */
    public IContextInformationValidator getContextInformationValidator()
    {
        return null;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getErrorMessage()
     */
    public String getErrorMessage()
    {
        return null;
    }

}
