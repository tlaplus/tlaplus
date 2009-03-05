package de.techjava.tla.ui.editors.completion;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ContextInformation;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.text.contentassist.IContextInformationPresenter;
import org.eclipse.jface.text.contentassist.IContextInformationValidator;

import de.techjava.tla.ui.editors.util.ITLAOperators;
import de.techjava.tla.ui.editors.util.ITLAReserveredWords;

/**
 * Completion processor for TLA source code
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLASourceCompletionProcessor.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public class TLASourceCompletionProcessor 
	implements IContentAssistProcessor 
{

    protected IContextInformationValidator validator= new Validator();
    /**
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#computeCompletionProposals(org.eclipse.jface.text.ITextViewer, int)
     */
    public ICompletionProposal[] computeCompletionProposals(
            ITextViewer viewer, 
            int documentOffset) 
    {
        
		List 	results	= new ArrayList(ITLAOperators.ALL_OPERATOR_SET.size() + ITLAReserveredWords.ALL_WORDS_SET.size());
		Vector 	allOps  = new Vector(ITLAOperators.ALL_OPERATOR_SET);
		
		Vector	all		= new Vector(allOps);
		all.addAll(ITLAReserveredWords.ALL_WORDS_SET);
		
		Iterator iter	= all.iterator();
		while (iter.hasNext()) 
		{
			addProposal((String)iter.next(), viewer, documentOffset, results, true);
		}
		if (results.isEmpty()) 
		{
			iter = all.iterator();
			while (iter.hasNext())
			{
				// addProposal((String)iter.next(), viewer, documentOffset, results, false);
			}
		}

		return (ICompletionProposal[])results.toArray(new ICompletionProposal[results.size()]);
    }
    /**
     * Adds a proposal to list
     * @param proposal
     * @param viewer
     * @param documentOffset
     * @param results
     * @param filter
     */
    private void addProposal(
            String proposal, 
            ITextViewer viewer, 
            int documentOffset, 
            List results, 
            boolean filter) 
    {
		// compute correct replacement
		if (filter) 
		{
			String selection = null;
			try 
			{
				selection = viewer.getDocument().get(documentOffset - 1, 1);
				if (selection == null 
				        || selection.length() 	== 0 
				        || proposal.length() 	== 0
				        || proposal.charAt(0) 	!= selection.charAt(0)
				    )
				{
					return;			    
				}

				proposal = proposal.substring(1);

			} catch (BadLocationException e) 
			{
				return ;
			}
		}

		String displayString		= proposal;
		String additionalInfo		= proposal;
		IContextInformation info	= createContextInformation(proposal);

		int relativeOffset= proposal.length();
		results.add(new CompletionProposal(proposal, documentOffset, 0, Math.max(0, relativeOffset), null, displayString, info, additionalInfo));
	}

    private IContextInformation createContextInformation(String proposal)
    {
        return new ContextInformation(proposal, proposal);
    }
    
    /**
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#computeContextInformation(org.eclipse.jface.text.ITextViewer, int)
     */
    public IContextInformation[] computeContextInformation(
            ITextViewer viewer, 
            int documentOffset) 
    {
        // TODO what is this for ?
        IContextInformation[] result = new IContextInformation[5];
    	for (int i = 0; i < result.length; i++)
    	{
    		result[i]= new ContextInformation( "test" + i, "test2" );
    	}
    	return result;
    }

    /**
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getCompletionProposalAutoActivationCharacters()
     */
    public char[] getCompletionProposalAutoActivationCharacters() 
    {
		return new char[] { ' ', '\\' };
	}

    /**
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getContextInformationAutoActivationCharacters()
     */
	public char[] getContextInformationAutoActivationCharacters() 
	{
	    // TODO what is this for ?
		return new char[] { '#' };
	}

    /**
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getErrorMessage()
     */
    public String getErrorMessage() 
    {
        return "Error";
    }

    /**
     * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getContextInformationValidator()
     */
	public IContextInformationValidator getContextInformationValidator() 
	{
		return validator;
	}

	/**
	 * Simple content assist tip closer. The tip is valid in a range
	 * of 5 characters around its popup location.
	 */
	protected static class Validator 
		implements IContextInformationValidator, IContextInformationPresenter 
	{

		protected int installOffset;

		/*
		 * @see IContextInformationValidator#isContextInformationValid(int)
		 */
		public boolean isContextInformationValid(int offset) 
		{
			return Math.abs(installOffset - offset) < 5;
		}

		/*
		 * @see IContextInformationValidator#install(IContextInformation, ITextViewer, int)
		 */
		public void install(IContextInformation info, ITextViewer viewer, int offset) 
		{
			installOffset= offset;
		}
		
		/*
		 * @see org.eclipse.jface.text.contentassist.IContextInformationPresenter#updatePresentation(int, TextPresentation)
		 */
		public boolean updatePresentation(int documentPosition, TextPresentation presentation) 
		{
			return false;
		}
	}

}

/*
 * $Log: TLASourceCompletionProcessor.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.2  2004/10/20 22:42:31  sza
 * editor improvements
 *
 * Revision 1.1  2004/10/13 19:27:50  sza
 * init
 *
 *
 */