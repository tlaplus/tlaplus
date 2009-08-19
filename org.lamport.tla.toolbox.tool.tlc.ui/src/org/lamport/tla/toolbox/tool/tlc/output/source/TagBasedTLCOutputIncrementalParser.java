package org.lamport.tla.toolbox.tool.tlc.output.source;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.DocumentPartitioningChangedEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.IDocumentPartitioningListener;
import org.eclipse.jface.text.IDocumentPartitioningListenerExtension2;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
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

    /**
     * The listener interested in change of partitioning, which evaluates the partitioning and produces the TLCOutput (added to the source)
     */
    class TLCOutputPartitionChangeListener implements IDocumentPartitioningListener,
            IDocumentPartitioningListenerExtension2
    {
        public void documentPartitioningChanged(IDocument document)
        {
        }

        public void documentPartitioningChanged(DocumentPartitioningChangedEvent event)
        {
            IDocument document = event.getDocument();

            IRegion changedRegion = event.getCoverage();
            IDocumentPartitioner partitioner = document.getDocumentPartitioner();

            // read the new partitioning information
            ITypedRegion[] regions = partitioner.computePartitioning(lastPartitionEnd, changedRegion.getOffset()
                    + changedRegion.getLength());

            // iterate partitions and look for the last
            // non-default (user-output) partition

            analyzer.resetUserPartitions();
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
                        // user partitions found, which are not belonging to the tag.
                        if (analyzer.hasUserPartitions() && !analyzer.inTag())
                        {
                            ITypedRegion mergedPartition = analyzer.getUserRegion();
                            source.onOutput(mergedPartition);
                            PartitionToolkit.printPartition(mergedPartition, document);
                        }

                        // START_TAG
                        // just add the partition to the analyzer
                        analyzer.addTagStart(regions[i]);
                    } else if (TagBasedTLCOutputTokenScanner.TAG_CLOSED.equals(regions[i].getType()))
                    {
                        // END TAG
                        // if the end is detected, everything between the start and
                        // the end are merged to a single tag
                        analyzer.addTagEnd(regions[i]);

                        // only if there are no nested tags, retrieve the tag, else,
                        // wait until the nesting tag is closed
                        if (!analyzer.inTag())
                        {
                            ITypedRegion tag = analyzer.getTaggedRegion();

                            // add the typed coverage region
                            source.onOutput(tag);
                        }
                    } else
                    {
                        // if the type is not default and neither START nor END, this is a bug
                        Assert.isTrue(regions[i].getLength() == 0, "Parsing bug");
                    }
                } else
                {
                    // if the partition has no type (default one), it is the user partition...
                    analyzer.addUserRegion(regions[i]);
                }
            }
        }
    }

    /**
     * Constructs the parser
     * @param name
     * @param prio
     */
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

        // now register the listener, responsible for evaluating the partitioning information
        document.addDocumentPartitioningListener(new TLCOutputPartitionChangeListener());

        // register the process source
        TLCOutputSourceRegistry.getStatusRegistry().addTLCStatusSource(this.source);
    }

    /**
     * add the increment
     * @param text
     * @throws BadLocationException
     */
    public void addIncrement(String text) throws BadLocationException
    {
        IDocument document = this.source.getDocument();
        document.replace(document.getLength(), 0, text);
    }

    /**
     * Finish
     */
    public void done()
    {
        this.source.onDone();
    }

    /**
     * Return the source
     */
    public ITLCOutputSource getSource()
    {
        return this.source;
    }

}
