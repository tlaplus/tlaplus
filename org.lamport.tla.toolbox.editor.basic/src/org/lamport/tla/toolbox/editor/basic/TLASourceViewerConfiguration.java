package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.BufferedRuleBasedScanner;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;

/**
 * Configuration of the source viewer for TLA+ editor 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLASourceViewerConfiguration extends SourceViewerConfiguration
{

    public IPresentationReconciler getPresentationReconciler(ISourceViewer sourceViewer)
    {
        TLAColorProvider provider = TLAEditorActivator.getDefault().getTLAColorProvider();
        PresentationReconciler reconciler = new PresentationReconciler();
        reconciler.setDocumentPartitioning(getConfiguredDocumentPartitioning(sourceViewer));

        DefaultDamagerRepairer dr = new DefaultDamagerRepairer(TLAEditorActivator.getDefault().getTLACodeScanner());
        reconciler.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
        reconciler.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);

        dr = new DefaultDamagerRepairer(new SingleTokenScanner(new TextAttribute(provider
                .getColor(TLAColorProvider.COMMENT))));
        reconciler.setDamager(dr, TLAPartitionScanner.TLA_COMMENT);
        reconciler.setRepairer(dr, TLAPartitionScanner.TLA_COMMENT);

        dr = new DefaultDamagerRepairer(new SingleTokenScanner(new TextAttribute(provider
                .getColor(TLAColorProvider.MULTI_LINE_COMMENT))));
        reconciler.setDamager(dr, TLAPartitionScanner.TLA_MULTILINE_COMMENT);
        reconciler.setRepairer(dr, TLAPartitionScanner.TLA_MULTILINE_COMMENT);

        return reconciler;
    }

    /**
     * Single token scanner.
     */
    public static class SingleTokenScanner extends BufferedRuleBasedScanner
    {
        public SingleTokenScanner(TextAttribute attribute)
        {
            setDefaultReturnToken(new Token(attribute));
        }
    }

    public String getConfiguredDocumentPartitioning(ISourceViewer sourceViewer)
    {
        return TLAPartitionScanner.TLA_PARTITIONING;
    }

    /**
     * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getConfiguredContentTypes(org.eclipse.jface.text.source.ISourceViewer)
     */
    public String[] getConfiguredContentTypes(ISourceViewer sourceViewer)
    {
        return new String[] { IDocument.DEFAULT_CONTENT_TYPE, TLAPartitionScanner.TLA_COMMENT,
                TLAPartitionScanner.TLA_MULTILINE_COMMENT };
    }
}
