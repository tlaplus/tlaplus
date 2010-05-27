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
 * 
 * @author Daniel Ricketts
 *
 */
public class ObligationSourceViewerConfiguration extends SourceViewerConfiguration
{

    public IPresentationReconciler getPresentationReconciler(ISourceViewer sourceViewer)
    {
        PresentationReconciler reconciler = new PresentationReconciler();

        DefaultDamagerRepairer dr = new DefaultDamagerRepairer(TLAEditorActivator.getDefault().getTLACodeScanner());
        reconciler.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
        reconciler.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);

        return reconciler;
    }

}
