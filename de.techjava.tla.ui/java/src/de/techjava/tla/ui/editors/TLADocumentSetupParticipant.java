package de.techjava.tla.ui.editors;

import org.eclipse.core.filebuffers.IDocumentSetupParticipant;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.rules.DefaultPartitioner;

import de.techjava.tla.ui.UIPlugin;
import de.techjava.tla.ui.editors.scanner.TLAPartitionScanner;

/**
 * Setups a document
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLADocumentSetupParticipant.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public class TLADocumentSetupParticipant 
	implements IDocumentSetupParticipant 
{

    /**
     * @see org.eclipse.core.filebuffers.IDocumentSetupParticipant#setup(org.eclipse.jface.text.IDocument)
     */
    public void setup(IDocument document) 
    {
		if (document instanceof IDocumentExtension3) {
			IDocumentExtension3 extension3= (IDocumentExtension3) document;
			IDocumentPartitioner partitioner = new DefaultPartitioner(UIPlugin.getDefault().getTLAPartitionScanner(), TLAPartitionScanner.TLA_PARTITION_TYPES);
			extension3.setDocumentPartitioner(TLAPartitionScanner.TLA_PARTITIONING, partitioner);
			partitioner.connect(document);
		}
    }

}

/*
 * $Log: TLADocumentSetupParticipant.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/13 19:29:56  sza
 * init
 *
 *
 */