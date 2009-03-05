package de.techjava.tla.ui.editors.completion;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ContextInformation;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.text.contentassist.IContextInformationValidator;
import org.eclipse.swt.graphics.Point;

import de.techjava.tla.ui.editors.util.ITLAOperators;
import de.techjava.tla.ui.editors.util.ITLAReserveredWords;

/**
 * Completion proporsal for TLA+ Editor
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLAEditorCompletionProcessor.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public class TLAEditorCompletionProcessor 
	implements IContentAssistProcessor
{

    private String[] allProposals;
    
    public TLAEditorCompletionProcessor()
    {
        try 
        {
            allProposals = new String[ITLAOperators.ALL_OPERATOR_ARRAY.length + ITLAReserveredWords.ALL_WORDS_ARRAY.length];
            System.arraycopy(ITLAReserveredWords.ALL_WORDS_ARRAY, 0, allProposals, 0, ITLAReserveredWords.ALL_WORDS_ARRAY.length);
            System.arraycopy(ITLAOperators.ALL_OPERATOR_ARRAY, 0, allProposals, ITLAReserveredWords.ALL_WORDS_ARRAY.length, ITLAOperators.ALL_OPERATOR_ARRAY.length);
            Arrays.sort(allProposals);
            
        } catch (Exception e) 
        {
            e.printStackTrace();
        }
    }

    /**
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#computeCompletionProposals(org.eclipse.jface.text.ITextViewer, int)
     */
    public ICompletionProposal[] computeCompletionProposals(ITextViewer viewer, int documentOffset) 
    {

        IDocument document = viewer.getDocument();
        Point selectedRange = viewer.getSelectedRange();
        
        List propList = new ArrayList();
        if (selectedRange.y > 0) 
        {
            try 
            {
                String text = document.get(selectedRange.x, selectedRange.y);
                computeOperatorProposals(text, documentOffset, propList);
            } catch (BadLocationException ble)
            {
                
            }
        } else {
            String qualifier = getOperator(document, documentOffset);
            computeOperatorProposals(qualifier, documentOffset, propList);
        }
        
        ICompletionProposal[] proposals = new ICompletionProposal[propList.size()];
        propList.toArray(proposals);
        
        return proposals;
    }

    
    /**
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#computeContextInformation(org.eclipse.jface.text.ITextViewer, int)
     */
    public IContextInformation[] computeContextInformation(ITextViewer viewer, int documentOffset) 
    {
        //      Retrieve selected range
        Point selectedRange = viewer.getSelectedRange();
        if (selectedRange.y > 0) 
        {

           // Text is selected. Create a context information array.
           ContextInformation[] contextInfos = new ContextInformation[ITLAReserveredWords.ALL_WORDS_ARRAY.length];

           // Create one context information item for each style
           for (int i = 0; i < ITLAReserveredWords.ALL_WORDS_ARRAY.length; i++)
              contextInfos[i] = new ContextInformation(null, ITLAReserveredWords.ALL_WORDS_ARRAY[i]+" Style");
           return contextInfos;

        }
        return new ContextInformation[0];
    }

    /**
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getCompletionProposalAutoActivationCharacters()
     */
    public char[] getCompletionProposalAutoActivationCharacters() 
    {
        return new char[]{' ', '\\'};
    }

    /**
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getContextInformationAutoActivationCharacters()
     */
    public char[] getContextInformationAutoActivationCharacters() 
    {
        return null;
    }

    /**
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getErrorMessage()
     */
    public String getErrorMessage() 
    {
        return null;
    }

    /**
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getContextInformationValidator()
     */
    public IContextInformationValidator getContextInformationValidator() 
    {
        return null;
    }
    
    
    /**
     * Retrieves a operator
     * @param document
     * @param documentOffset
     * @return
     */
    private String getOperator(IDocument document, int documentOffset) 
    {

        // Use string buffer to collect characters
        StringBuffer buffer = new StringBuffer("");
        while (true) 
        {
          try {

            // Read character backwards
            char c = document.getChar(--documentOffset);

            // This was not the start of a tag
            if ( Character.isWhitespace(c) )
               break;

            // Collect character
            buffer.append(c);

            // Start of tag. Return qualifier
            if (c == '\\')
                break;

          } catch (BadLocationException e) 
          {

            // Document start reached, no tag found
            break;
          }
        }
        
        return buffer.reverse().toString();
     }
    
    private void computeOperatorProposals(String qualifier, int documentOffset, List propList) 
    { 
        int qlen = qualifier.length();

        
        // Loop through all proposals
        for (int i = 0; i < allProposals.length; i++) 
        {
           String startTag = allProposals[i];

           // Check if proposal matches qualifier
           if (startTag.startsWith(qualifier)) 
           {

              // Yes -- compute whole proposal text
              String text = startTag + " ";

              // Derive cursor position
              int cursor = startTag.length();

              // Construct proposal
              CompletionProposal proposal = new CompletionProposal(text, documentOffset - qlen, qlen, cursor);

              // and add to result list
              propList.add(proposal);
           }
        }
    }
}

/*
 * $Log: TLAEditorCompletionProcessor.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/20 22:42:31  sza
 * editor improvements
 *
 *
 */