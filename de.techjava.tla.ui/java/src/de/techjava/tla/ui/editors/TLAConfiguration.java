package de.techjava.tla.ui.editors;

import org.eclipse.jface.text.DefaultAutoIndentStrategy;
import org.eclipse.jface.text.DefaultInformationControl;
import org.eclipse.jface.text.IAutoIndentStrategy;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IInformationControl;
import org.eclipse.jface.text.IInformationControlCreator;
import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.ITextHover;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.contentassist.ContentAssistant;
import org.eclipse.jface.text.contentassist.IContentAssistant;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.BufferedRuleBasedScanner;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.source.IAnnotationHover;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;

import de.techjava.tla.ui.UIPlugin;
import de.techjava.tla.ui.editors.annotation.TLAAnnotationHover;
import de.techjava.tla.ui.editors.annotation.TLATextHover;
import de.techjava.tla.ui.editors.completion.TLAEditorCompletionProcessor;
import de.techjava.tla.ui.editors.scanner.TLAPartitionScanner;
import de.techjava.tla.ui.util.ColorManager;
import de.techjava.tla.ui.util.IColorManagerListener;
import de.techjava.tla.ui.util.ITLAEditorColorConstants;


/**
 * Configuration toolkit
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLAConfiguration.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public class TLAConfiguration 
	extends SourceViewerConfiguration 
	implements IColorManagerListener
{
	private ColorManager 						colorManager;
	private TLADoubleClickStrategy 				doubleClickStrategy;
	
	private Color								colorContextInformationPopupBackground;
	private Color								colorCommentMultiLine;
	private Color								colorComment;
	
	
    private static final DefaultInformationControl.IInformationPresenter presenter = new DefaultInformationControl.IInformationPresenter() 
    {
       public String updatePresentation(
               Display display, 
               String infoText,
               TextPresentation presentation, 
               int maxWidth, 
               int maxHeight) 
       {
          int start = -1;

          // Loop over all characters of information text
          for (int i = 0; i < infoText.length(); i++) {
             switch (infoText.charAt(i)) {
                case '\\' :

                   // Remember start of tag
                   start = i;
                   break;
                case ' ' :
                   if (start >= 0) 
                   {

                     // We have found a tag and create a new style range
                     StyleRange range = 
                        new StyleRange(start, i - start + 1, null, null, SWT.BOLD);

                     // Add this style range to the presentation
                     presentation.addStyleRange(range);

                     // Reset tag start indicator
                     start = -1;
                   }
                   break;
          }
       }

       // Return the information text

       return infoText;
    }
 };
	
	
    /**
     * Default constructor
     * @param colorManager
     */
    public TLAConfiguration(ColorManager colorManager)
    {
        this.colorManager = colorManager;
        this.colorManager.addColorManagerListener(this);
        this.initializeColors();
    }
    

    /**
     * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getAnnotationHover(org.eclipse.jface.text.source.ISourceViewer)
     */
    public IAnnotationHover getAnnotationHover(ISourceViewer sourceViewer) 
    {
        return new TLAAnnotationHover();
    }
	/**
	 * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getConfiguredDocumentPartitioning(org.eclipse.jface.text.source.ISourceViewer)
	 */
	public String getConfiguredDocumentPartitioning(ISourceViewer sourceViewer) {
		return TLAPartitionScanner.TLA_PARTITIONING;
	}

    /**
     * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getConfiguredContentTypes(org.eclipse.jface.text.source.ISourceViewer)
     */
    public String[] getConfiguredContentTypes(ISourceViewer sourceViewer) 
    {
        return new String[] {
              IDocument.DEFAULT_CONTENT_TYPE,
              TLAPartitionScanner.TLA_COMMENT,
              TLAPartitionScanner.TLA_COMMENT_MULTI
        };
    }
	/**
	 * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getContentAssistant(org.eclipse.jface.text.source.ISourceViewer)
	 */
    public IContentAssistant getContentAssistant(ISourceViewer sourceViewer) 
    {
        ContentAssistant assistant= new ContentAssistant();
        assistant.setDocumentPartitioning(getConfiguredDocumentPartitioning(sourceViewer));
        assistant.setContentAssistProcessor(new TLAEditorCompletionProcessor(), IDocument.DEFAULT_CONTENT_TYPE);
    	assistant.setInformationControlCreator(getInformationControlCreator(sourceViewer));
		assistant.enableAutoActivation(true);
		assistant.setAutoActivationDelay(500);
		assistant.setProposalPopupOrientation(IContentAssistant.PROPOSAL_OVERLAY);
		assistant.setContextInformationPopupOrientation(IContentAssistant.CONTEXT_INFO_ABOVE);
		assistant.setContextInformationPopupBackground(this.colorContextInformationPopupBackground);

        return assistant;
    }
    /**
     * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getDoubleClickStrategy(org.eclipse.jface.text.source.ISourceViewer, java.lang.String)
     */
	public ITextDoubleClickStrategy getDoubleClickStrategy(
			ISourceViewer sourceViewer,
			String contentType) 
	{
			if (doubleClickStrategy == null)
				doubleClickStrategy = new TLADoubleClickStrategy();
			return doubleClickStrategy;
	}
	/**
	 * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getPresentationReconciler(org.eclipse.jface.text.source.ISourceViewer)
	 */
	public IPresentationReconciler getPresentationReconciler(ISourceViewer sourceViewer) 
	{
	    PresentationReconciler reconciler = new PresentationReconciler();
		reconciler.setDocumentPartitioning(getConfiguredDocumentPartitioning(sourceViewer));
		
		DefaultDamagerRepairer damageRepairer = new DefaultDamagerRepairer(UIPlugin.getDefault().getTLASourceScanner());
		reconciler.setDamager(damageRepairer, IDocument.DEFAULT_CONTENT_TYPE);
		reconciler.setRepairer(damageRepairer, IDocument.DEFAULT_CONTENT_TYPE);
		
		damageRepairer= new DefaultDamagerRepairer(new SingleTokenScanner(new TextAttribute(this.colorComment)));
		reconciler.setDamager(damageRepairer, TLAPartitionScanner.TLA_COMMENT);
		reconciler.setRepairer(damageRepairer, TLAPartitionScanner.TLA_COMMENT);

		damageRepairer= new DefaultDamagerRepairer(new SingleTokenScanner(new TextAttribute(this.colorCommentMultiLine)));
		reconciler.setDamager(damageRepairer, TLAPartitionScanner.TLA_COMMENT_MULTI);
		reconciler.setRepairer(damageRepairer, TLAPartitionScanner.TLA_COMMENT_MULTI);

		return reconciler;
	}
	/**
	 * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getTextHover(org.eclipse.jface.text.source.ISourceViewer, java.lang.String, int)
	 */
    public ITextHover getTextHover(ISourceViewer sourceViewer, String contentType, int stateMask) 
    {
        return new TLATextHover();
    }
    
    
    /**
     * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getInformationControlCreator(org.eclipse.jface.text.source.ISourceViewer)
     */
    public IInformationControlCreator getInformationControlCreator(
            ISourceViewer sourceViewer) 
    {
        
        return new IInformationControlCreator() 
        {

            public IInformationControl createInformationControl(Shell parent) {
                return new DefaultInformationControl(parent, presenter);
            }
            
        };
    }

    
    /**
     * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getAutoIndentStrategy(org.eclipse.jface.text.source.ISourceViewer, java.lang.String)
     */
    public IAutoIndentStrategy getAutoIndentStrategy(ISourceViewer sourceViewer, String contentType) 
    {
        return new DefaultAutoIndentStrategy();
    }
    /**
     * @see de.techjava.tla.ui.util.IColorManagerListener#colorManagerChanged()
     */
    public void colorManagerChanged() 
    {
        initializeColors();
    }
    
    /**
     * Initializes the colors
     */
    private void initializeColors() 
    {
        this.colorContextInformationPopupBackground = colorManager.getColor(ITLAEditorColorConstants.CTX_INFORMATION_POPUP_BG);
        this.colorCommentMultiLine					= colorManager.getColor(ITLAEditorColorConstants.COMMENT_MULTILINE);
        this.colorComment							= colorManager.getColor(ITLAEditorColorConstants.COMMENT);
    }

    /**
     * Single toke scanner 
     * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
     * @version $Id: TLAConfiguration.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
     */
	static class SingleTokenScanner 
		extends BufferedRuleBasedScanner 
	{
		public SingleTokenScanner(TextAttribute attribute) 
		{
			setDefaultReturnToken(new Token(attribute));
		}
	}
	
}

/*
 * $Log: TLAConfiguration.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.6  2004/10/24 23:11:52  sza
 * indention added
 *
 * Revision 1.5  2004/10/20 22:42:31  sza
 * editor improvements
 *
 * Revision 1.4  2004/10/13 23:12:17  sza
 * hovers
 *
 * Revision 1.3  2004/10/13 19:30:05  sza
 * refactored
 *
 * Revision 1.2  2004/10/13 14:45:00  sza
 * operators added
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:12  sza
 * additions
 *
 * Revision 1.1  2004/10/06 01:02:29  sza
 * initial commit
 *
 * Revision 1.1  2004/10/06 00:59:05  sza
 * initial commit
 *
 *
 */