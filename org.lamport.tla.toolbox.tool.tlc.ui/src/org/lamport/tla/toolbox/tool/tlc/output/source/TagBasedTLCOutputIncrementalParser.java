package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.Vector;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.TypedRegion;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.lamport.tla.toolbox.tool.tlc.output.PartitionToolkit;

/**
 * Incremental parser based on TLC output in tags
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TagBasedTLCOutputIncrementalParser
{
    private int lastPartitionEnd;
    private TagBasedTLCAnalyzer analyzer;
    private CachingTLCOutputSource source;

    public TagBasedTLCOutputIncrementalParser(String name, int prio)
    {
        // create the document
        Document document = new Document();

        this.analyzer = new TagBasedTLCAnalyzer(document);
        this.source = new CachingTLCOutputSource(name, prio);


        // set up the partitioner
        FastPartitioner partitioner = new FastPartitioner(new TagBasedTLCOutputTokenScanner(),
                TagBasedTLCOutputTokenScanner.CONTENT_TYPES);
        partitioner.connect(document);
        document.setDocumentPartitioner(partitioner);

        this.source.setDocument(document);

        // register the process source
        TLCOutputSourceRegistry.getStatusRegistry().addTLCStatusSource(this.source);
    }

    public void addIncrement(String text) throws BadLocationException
    {
        IDocument document = this.source.getDocument();
        // add the increment
        document.replace(document.getLength(), 0, text);

        IDocumentPartitioner partitioner = document.getDocumentPartitioner();
        int startOfUnpartitionedText = Math.min(document.getLength(), lastPartitionEnd);

        System.out.println("Parsing from " + startOfUnpartitionedText + " to " + document.getLength());
        ITypedRegion[] regions = partitioner.computePartitioning(startOfUnpartitionedText, document.getLength());

        Vector userTempPartitions = new Vector();
        // iterate partitions and look for the last
        // non-default (user-output) partition
        for (int i = 0; i < regions.length; i++)
        {
            // looking for non-default content type
            if (!TagBasedTLCOutputTokenScanner.DEFAULT_CONTENT_TYPE.equals(regions[i].getType()))
            {
                // typed partition detected
                int currentPartitionEnd = regions[i].getOffset() + regions[i].getLength();
                if (currentPartitionEnd > lastPartitionEnd)
                {
                    lastPartitionEnd = currentPartitionEnd;
                }

                if (TagBasedTLCOutputTokenScanner.TAG_OPEN.equals(regions[i].getType()))
                {
                    // just add the partition to the analyzer
                    analyzer.addTagStart(regions[i]);
                }

                if (TagBasedTLCOutputTokenScanner.TAG_CLOSED.equals(regions[i].getType()))
                {
                    // if the coverage end is detected, everything between the start and
                    // the end are not user partitions, but
                    // coverage information
                    analyzer.addTagEnd(regions[i]);

                    ITypedRegion tag = analyzer.getTaggedRegion();
                    // add the typed coverage region
                    source.onOutput(tag);

                    // re-initialize the user partitions
                    userTempPartitions = new Vector();
                } else
                {

                    // user partitions found
                    if (userTempPartitions.size() > 1)
                    {
                        int startLine = document.getLineOfOffset(((TypedRegion) userTempPartitions.elementAt(0))
                                .getOffset());
                        int endLine = document.getLineOfOffset(((TypedRegion) userTempPartitions
                                .elementAt(userTempPartitions.size() - 1)).getOffset());
                        ITypedRegion mergedPartition = PartitionToolkit
                                .mergePartitions((ITypedRegion[]) userTempPartitions
                                        .toArray(new TypedRegion[userTempPartitions.size()]));
                        System.out.println("Merged " + userTempPartitions.size() + " user partitions. Lines from "
                                + startLine + " to " + endLine + ".");
                        source.onOutput(mergedPartition);
                        PartitionToolkit.printPartition(mergedPartition, document);

                        // re-initialize the user partitions
                        userTempPartitions = new Vector();
                    }
                    
                    
                    if (!TagBasedTLCOutputTokenScanner.TAG_OPEN.equals(regions[i].getType()))
                    {
                        // the partition after the user partition
                        // but not the tag start partition
                        source.onOutput(regions[i]);
                    }

                }
            } else
            {
                // if the partition has no type (default one), it is the user partition...
                userTempPartitions.add(regions[i]);
            }
        }
    }

    public void done()
    {
        this.source.onDone();
    }

    /**
     * 
     * @return
     */
    public ITLCOutputSource getSource()
    {
        return this.source;
    }
}
