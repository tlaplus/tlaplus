package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextAttribute;
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
import org.lamport.tla.toolbox.editor.basic.tla.TLAAnnotationHover;
import org.lamport.tla.toolbox.editor.basic.tla.TLACompletionProcessor;

/**
 * Configuration of the source viewer for TLA+ editor 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLASourceViewerConfiguration extends SourceViewerConfiguration
{
    /**
     * Constructor
     */
    public TLASourceViewerConfiguration() 
    {
    }

    /**
     * Reconciler setup
     */
    public IPresentationReconciler getPresentationReconciler(ISourceViewer sourceViewer)
    {
        TLAColorProvider provider = TLAEditorActivator.getDefault().getTLAColorProvider();
        PresentationReconciler reconciler = new PresentationReconciler();
        reconciler.setDocumentPartitioning(getConfiguredDocumentPartitioning(sourceViewer));

        DefaultDamagerRepairer dr = new DefaultDamagerRepairer(TLAEditorActivator.getDefault().getTLACodeScanner());
        reconciler.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
        reconciler.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);

        dr = new DefaultDamagerRepairer(new SingleTokenScanner(new TextAttribute(provider
                .getColor(TLAColorProvider.MULTI_LINE_COMMENT))));
        reconciler.setDamager(dr, TLAPartitionScanner.TLA_MULTILINE_COMMENT);
        reconciler.setRepairer(dr, TLAPartitionScanner.TLA_MULTILINE_COMMENT);

        
        return reconciler;
    }

    /**
     * Partitioning
     */
    public String getConfiguredDocumentPartitioning(ISourceViewer sourceViewer)
    {
        return TLAPartitionScanner.TLA_PARTITIONING;
    }

    /**
     * Configured content types
     */
    public String[] getConfiguredContentTypes(ISourceViewer sourceViewer)
    {
        return new String[] { IDocument.DEFAULT_CONTENT_TYPE, TLAPartitionScanner.TLA_MULTILINE_COMMENT};
    }
    
    
    /**
     * Content assistant
     */
    public IContentAssistant getContentAssistant(ISourceViewer sourceViewer) {

        ContentAssistant assistant= new ContentAssistant();
        assistant.setDocumentPartitioning(getConfiguredDocumentPartitioning(sourceViewer));
        assistant.setContentAssistProcessor(new TLACompletionProcessor(), IDocument.DEFAULT_CONTENT_TYPE);
        assistant.enableAutoActivation(true);
        assistant.setAutoActivationDelay(500);
        assistant.setProposalPopupOrientation(IContentAssistant.PROPOSAL_OVERLAY);
        assistant.setContextInformationPopupOrientation(IContentAssistant.CONTEXT_INFO_ABOVE);
        assistant.setContextInformationPopupBackground(TLAEditorActivator.getDefault().getTLAColorProvider().getColor(TLAColorProvider.CONTENT_ASSIST_BACKGROUNG));
        return assistant;
    }
    
    /**
     * Single token scanner, returns attributed token
     */
    public static class SingleTokenScanner extends BufferedRuleBasedScanner
    {
        public SingleTokenScanner(TextAttribute attribute)
        {
            setDefaultReturnToken(new Token(attribute));
        }
    }

    public IAnnotationHover getAnnotationHover(ISourceViewer sourceViewer)
    {
        return new TLAAnnotationHover();
    }

}
