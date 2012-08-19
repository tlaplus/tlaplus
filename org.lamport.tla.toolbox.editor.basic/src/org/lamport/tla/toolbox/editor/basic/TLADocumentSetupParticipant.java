package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.core.filebuffers.IDocumentSetupParticipant;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.rules.FastPartitioner;

/**
 * Responsible for document setup
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLADocumentSetupParticipant implements IDocumentSetupParticipant
{
    public void setup(IDocument document) {
        if (document instanceof IDocumentExtension3) {
            IDocumentExtension3 extension3= (IDocumentExtension3) document;
            IDocumentPartitioner partitioner= new TLAFastPartitioner(TLAEditorActivator.getDefault().getTLAPartitionScanner(), TLAPartitionScanner.TLA_PARTITION_TYPES);
                                                // Changed from FastPartitioner by LL on 12 Aug 2012
            extension3.setDocumentPartitioner(TLAPartitionScanner.TLA_PARTITIONING, partitioner);
            partitioner.connect(document);
        }
    }
}
