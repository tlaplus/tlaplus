package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.contentassist.ContentAssistant;
import org.eclipse.jface.text.contentassist.IContentAssistant;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.reconciler.IReconciler;
import org.eclipse.jface.text.reconciler.MonoReconciler;
import org.eclipse.jface.text.rules.BufferedRuleBasedScanner;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.source.IAnnotationHover;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.ui.editors.text.TextSourceViewerConfiguration;
import org.lamport.tla.toolbox.editor.basic.tla.TLAAnnotationHover;
import org.lamport.tla.toolbox.editor.basic.tla.TLACompletionProcessor;

/**
 * Configuration of the source viewer for TLA+ editor 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLASourceViewerConfiguration extends TextSourceViewerConfiguration
{

    private final TLAEditor editor;

    /**
     * Constructs configuration based on a preference store  
     * @param preferenceStore
     */
    public TLASourceViewerConfiguration(IPreferenceStore preferenceStore, TLAEditor editor)
    {
        super(preferenceStore);
        this.editor = editor;
    }

    /**
     * Reconciler setup
     * 
     * This is used to setup the text coloring. This is done by adding one or more damager-repairers
     * to the presentation reconciler returned by this method. Each damager-repairer is registered
     * for a specific content type. The text ranges that correspond to each content type
     * are computed using a partitioner. The partitioner for the document
     * held in the editor is setup in {@link TLADocumentSetupParticipant#setup(IDocument)}.
     * 
     * The partitioner computes the partitions at the appropriate times and then the various
     * damager-repairers set in this method compute the coloring for the partitions.
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
                .getColor(TLAColorProvider.TLA_MULTI_LINE_COMMENT))));
        reconciler.setDamager(dr, TLAPartitionScanner.TLA_MULTI_LINE_COMMENT);
        reconciler.setRepairer(dr, TLAPartitionScanner.TLA_MULTI_LINE_COMMENT);

        dr = new DefaultDamagerRepairer(new SingleTokenScanner(new TextAttribute(provider
                .getColor(TLAColorProvider.TLA_SINGLE_LINE_COMMENT))));
        reconciler.setDamager(dr, TLAPartitionScanner.TLA_SINGLE_LINE_COMMENT);
        reconciler.setRepairer(dr, TLAPartitionScanner.TLA_SINGLE_LINE_COMMENT);

        dr = new DefaultDamagerRepairer(new SingleTokenScanner(new TextAttribute(provider
                .getColor(TLAColorProvider.TLA_VALUE))));
        reconciler.setDamager(dr, TLAPartitionScanner.TLA_STRING);
        reconciler.setRepairer(dr, TLAPartitionScanner.TLA_STRING);

        // The following added for PlusCal
        dr = new DefaultDamagerRepairer(TLAEditorActivator.getDefault().getPCALCodeScanner());
        reconciler.setDamager(dr, TLAPartitionScanner.TLA_PCAL);
        reconciler.setRepairer(dr, TLAPartitionScanner.TLA_PCAL);

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
        return new String[] { IDocument.DEFAULT_CONTENT_TYPE, TLAPartitionScanner.TLA_MULTI_LINE_COMMENT,
                TLAPartitionScanner.TLA_SINGLE_LINE_COMMENT, TLAPartitionScanner.TLA_STRING,
                // Added by LL on 16 Aug 2012:  I don't know what this is all about, but
                // I presume we need to register the TLA_PCAL partition type here.
                TLAPartitionScanner.TLA_PCAL};  // Added for PlusCal
    }

    /**
     * Content assistant
     */
    public IContentAssistant getContentAssistant(ISourceViewer sourceViewer)
    {

        ContentAssistant assistant = new ContentAssistant();
        assistant.setDocumentPartitioning(getConfiguredDocumentPartitioning(sourceViewer));
        assistant.setContentAssistProcessor(new TLACompletionProcessor(), IDocument.DEFAULT_CONTENT_TYPE);
        assistant.enableAutoActivation(true);
        assistant.setAutoActivationDelay(500);
        assistant.setProposalPopupOrientation(IContentAssistant.PROPOSAL_OVERLAY);
        assistant.setContextInformationPopupOrientation(IContentAssistant.CONTEXT_INFO_ABOVE);
        assistant.setContextInformationPopupBackground(TLAEditorActivator.getDefault().getTLAColorProvider().getColor(
                TLAColorProvider.CONTENT_ASSIST_BACKGROUNG));
        return assistant;
    }

    /**
     * Ruler annotation
     */
    public IAnnotationHover getAnnotationHover(ISourceViewer sourceViewer)
    {
        return new TLAAnnotationHover();
    }

    /**
     * 
     */
    public IReconciler getReconciler(ISourceViewer sourceViewer)
    {
        TLAReconcilingStrategy strategy = new TLAReconcilingStrategy();
        strategy.setEditor(editor);
        MonoReconciler reconciler = new MonoReconciler(strategy, false);
        return reconciler;
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

    public String[] getDefaultPrefixes(ISourceViewer sourceViewer, String contentType)
    {
        return new String[] { "\\*", "" };
    }

}
