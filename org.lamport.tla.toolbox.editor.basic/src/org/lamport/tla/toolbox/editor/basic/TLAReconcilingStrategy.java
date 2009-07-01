package org.lamport.tla.toolbox.editor.basic;

import java.util.ArrayList;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.BadPartitioningException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.reconciler.DirtyRegion;
import org.eclipse.jface.text.reconciler.IReconcilingStrategy;
import org.eclipse.jface.text.reconciler.IReconcilingStrategyExtension;
import org.eclipse.swt.widgets.Display;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAReconcilingStrategy implements IReconcilingStrategy, IReconcilingStrategyExtension
{
    /* document to reconciler */
    private IDocument document;
    /* holds the calculated positions */
    protected final ArrayList positions = new ArrayList();
    /* editor to be updated */
    private TLAEditor editor;

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.reconciler.IReconcilingStrategy#reconcile(org.eclipse.jface.text.IRegion)
     */
    public void reconcile(IRegion partition)
    {
        initialReconcile();
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.reconciler.IReconcilingStrategy#reconcile(org.eclipse.jface.text.reconciler.DirtyRegion, org.eclipse.jface.text.IRegion)
     */
    public void reconcile(DirtyRegion dirtyRegion, IRegion subRegion)
    {
        initialReconcile();
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.reconciler.IReconcilingStrategy#setDocument(org.eclipse.jface.text.IDocument)
     */
    public void setDocument(IDocument document)
    {
        this.document = document;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.reconciler.IReconcilingStrategyExtension#initialReconcile()
     */
    public void initialReconcile()
    {
        // delete existing
        positions.clear();

        // calculate new partitions
        calculatePositions();

        // update the editor
        Display.getDefault().asyncExec(new Runnable() {
            public void run()
            {
                editor.updateFoldingStructure(positions);
            }
        });

    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.reconciler.IReconcilingStrategyExtension#setProgressMonitor(org.eclipse.core.runtime.IProgressMonitor)
     */
    public void setProgressMonitor(IProgressMonitor monitor)
    {

    }

    /**
     * @return Returns the editor.
     */
    public TLAEditor getEditor()
    {
        return this.editor;
    }

    /**
     * Sets the editor
     * @param editor
     */
    public void setEditor(TLAEditor editor)
    {
        this.editor = editor;
    }

    /**
     * get partitions  
     */
    protected void calculatePositions()
    {
        try
        {
            IDocumentExtension3 extension = (IDocumentExtension3) document;
            // get partitions
            ITypedRegion[] partitions = extension.computePartitioning(TLAPartitionScanner.TLA_PARTITIONING, 0, document
                    .getLength(), false);
            // install positions
            for (int i = 0; i < partitions.length; i++)
            {
                IRegion lineOnPartitionStart = document.getLineInformationOfOffset(partitions[i].getOffset());

                // if the multi-line comment contains multiple lines
                if (partitions[i].getType().equals(TLAPartitionScanner.TLA_MULTI_LINE_COMMENT)
                        && partitions[i].getLength() > lineOnPartitionStart.getLength())
                {
                    positions.add(new Position(partitions[i].getOffset(), partitions[i].getLength()));
                }
            }

        } catch (BadLocationException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (BadPartitioningException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

}
