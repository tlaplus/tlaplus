package org.lamport.tla.toolbox.tool.prover.ui.view;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;
import org.lamport.tla.toolbox.editor.basic.TLAEditorActivator;

/**
 * The configuration for source viewers displaying pretty-printed forms of obligations.
 * Uses the syntax highlighting of the tla editor.
 * 
 * @author Daniel Ricketts
 *
 */
public class ObligationSourceViewerConfiguration extends SourceViewerConfiguration
{

    /**
     * This registers one damager repairer for all content in the source viewer.
     * The damager-repairer scans the content for TLA keywords and sets them to the
     * same color used in the tla editor.
     */
    public IPresentationReconciler getPresentationReconciler(ISourceViewer sourceViewer)
    {
        PresentationReconciler reconciler = new PresentationReconciler();

        DefaultDamagerRepairer dr = new DefaultDamagerRepairer(TLAEditorActivator.getDefault().getTLACodeScanner());
        reconciler.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
        reconciler.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);

        return reconciler;
    }

}
