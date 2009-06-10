package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.core.filebuffers.IDocumentSetupParticipant;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.rules.FastPartitioner;

/**
 * Responsible for document setup
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLADocumentSetupParticipant implements IDocumentSetupParticipant
{

    public void setup(IDocument document)
    {
        IDocumentPartitioner partitioner = new FastPartitioner(
                TLAEditorActivator.getDefault().getTLAPartitionScanner(), TLAPartitionScanner.TLA_PARTITION_TYPES);
        partitioner.connect(document);

    }

}
