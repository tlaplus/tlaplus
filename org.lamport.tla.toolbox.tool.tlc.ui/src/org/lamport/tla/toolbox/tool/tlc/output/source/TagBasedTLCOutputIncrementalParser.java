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
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

/**
 * Incremental parser based on TLC output in tags.
 * 
 * Implementation:
 * When instantiated, this parser creates an {@link IDocument}.
 * As text streams in, it is appended to the end of this document.
 * 
 * Attached to the document is an {@link IDocumentPartitioner}
 * and a {@link IDocumentPartitioningListener}. The partitioner
 * breaks the document into partitions based on the rules defined in
 * the class {@link TagBasedTLCOutputTokenScanner}. Currently,
 * a partition is a line containing a start tag, a line containing an
 * end tag, or any single character not in one of those lines. So
 * consider the following document:
 * 
 * @!@!@STARTMSG 2221:0 @!@!@
 * example
 * @!@!@ENDMSG 2221 @!@!@
 * 
 * The partitions would be the {@link IRegion} describing the line
 * containing "@!@!@STARTMSG 2221:0 @!@!@", an {@link IRegion} for each
 * character in "example", and an {@link IRegion} describing the line
 * containing "@!@!@ENDMSG 2221 @!@!@".
 * 
 * As text is appended to the document, the partitioning changes. The
 * {@link IDocumentPartitioningListener} attached to the document is notified
 * of these changes.
 * 
 * The {@link IDocumentPartitioningListener} used is {@link TLCOutputPartitionChangeListener}.
 * The method {@link TLCOutputPartitionChangeListener#documentPartitioningChanged(DocumentPartitioningChangedEvent)}
 * does the work in analyzing the partitions. See that method for the implementation.
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TagBasedTLCOutputIncrementalParser
{
    /**
     * The offset of the end of the last
     * start or end tag seen by the previous run of
     * the method {@link TLCOutputPartitionChangeListener#documentPartitioningChanged(DocumentPartitioningChangedEvent)}.
     */
    private int lastPartitionEnd;
    private final TagBasedTLCAnalyzer analyzer;
    private final CachingTLCOutputSource source;
	private final Document document;

    /**
     * The listener interested in change of partitioning, which evaluates the partitioning and produces the TLCOutput (added to the source)
     */
    class TLCOutputPartitionChangeListener implements IDocumentPartitioningListener,
            IDocumentPartitioningListenerExtension2
    {
        public void documentPartitioningChanged(IDocument document)
        {
        }

        /**
         * Does the work in analyzing partitions to send output to the source.
         */
        public void documentPartitioningChanged(DocumentPartitioningChangedEvent event)
        {
            /*
             * Implementation:
             * 
             * For the purposes of this method, the parser maintains lastPartitionEnd and analyzer.
             * These are explained below:
             * 
             * -lastPartitionEnd, which represents the offset of the end of the last
             *  start or end tag seen by the previous run of this method. Initially,
             *  lastPartitionEnd = 0.
             * 
             * -TagBasedTLCAnalyzer. The analyzer maintains a stack
             *  of start and end tags and a list of partitions that are not
             *  start or end tags. The regions that are not start or end
             *  tags are called user regions. Whenever the stack is put in a state
             *  such that all start tags have a matching end tag, this should mean
             *  that there is one pair of start and end tags on the stack that contains
             *  all other start and end tags. At this point, the analyzer clears the stack
             *  and creates a region describing the pair of tags that encloses all others.
             *  This region can be obtained by calling analyzer.getTaggedRegion(). The analyzer
             *  should only clear the stack when the previous condition is true.
             * 
             * Take the following steps when this method is called:
             * 
             * 1.) Compute partitions from lastPartitionEnd to the end
             *     of the region described by event.getCoverage().
             * 2.) Clear the analyzer's list of user regions.
             * 3.) Once a portion of the document is sent to the source in
             *     the appropriate form, it should be removed from the document.
             *     This removal occurs in step 6. For this purpose, we have an
             *     integer, offsetToRemove, that initially equals 0.
             * 4.) For each partition computed in step (1), perform the following:
             *         IF (partition is a start or end tag)
             *            -IF (end of partition is greater than lastPartitionEnd)
             *                -lastPartitionEnd = end of partition
             *             END IF
             *         
             *             IF (partition is a start tag)
             *                -IF (stack is empty and list of user regions is not empty)
             *                    -merge user regions into one region and pass to source
             *                -push start tag on analyzer's stack
             *             ELSE IF (partition is an end tag)
             *                -push on analyzer's stack
             *                -IF (the analyzer's stack is empty)
             *                    -see the note towards the beginning of these
             *                     comments on how this is possible
             *                    -send a region describing the containing pair of tags
             *                     that were just removed from the analyzer's stack
             *                     to the source
             *                END IF
             *             END IF
             *             
             *         ELSE
             *            -add to analyzer's list of user regions
             *            
             *         END IF
             *         
             * 5.) IF (analyzer's stack is empty)
             *            -offsetToRemove = lastPartitionEnd
             *            -lastPartitionEnd = 0
             *     END IF
             *          
             * 6.) Remove everything in the document from the beginning to offsetToRemove if offsetToRemove > 0.
             * 
             * Note that it is possible for there to be a moment where the document does not end
             * with an end tag. In other words, this parser can receive incomplete messages. This requires
             * maintaining the lastPartitionEnd field so that the same start tag is not pushed onto the analyzer's
             * stack multiple times. The field lastPartitionEnd gives the end of the last partition that
             * is a start or end tags. It is not necessary to maintain the location of user regions because
             * they are reset in step (2).
             * 
             * We remove text from the document only when the analyzer's stack is empty (step 5). This is for the
             * following reason. The analyzer's stack contains regions that point to locations in the document.
             * They point to locations using an offset and length. The offset and length of a given region do
             * not change when the document changes. Therefore, we only want to modify the document once there
             * are no regions that need to access their locations in the document. When a region is sent to the
             * source, it no longer needs to access its location in the document because it is sent to the source
             * along with the contents of the message that it represents. However, when a region is stored in the
             * analyzer's stack, it is not stored with the contents of the message it represents, so it still
             * needs to access the document before being sent to the source. User regions are reset with
             * every call of this method, so text can be removed from the document at the end of this method
             * even if the list of regions in the analyzer is not empty.
             * 
             * 
             *             
             */

            IDocument document = event.getDocument();

            try
            {
                IRegion changedRegion = event.getCoverage();
                IDocumentPartitioner partitioner = document.getDocumentPartitioner();

                // read the new partitioning information (Step 1)
                ITypedRegion[] regions = partitioner.computePartitioning(lastPartitionEnd, changedRegion.getOffset()
                        + changedRegion.getLength() - lastPartitionEnd);

                // iterate partitions and look for the last
                // non-default (user-output) partition

                // Step 2
                analyzer.resetUserPartitions();

                // Step 3
                int offsetToRemove = 0;

                // Step 4
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
                                source.onOutput(mergedPartition, document.get(mergedPartition.getOffset(),
                                        mergedPartition.getLength()));
                                // debugging
                                // PartitionToolkit.printPartition(mergedPartition, document);
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
                                source.onOutput(tag, document.get(tag.getOffset(), tag.getLength()));
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

                // Step 5
                if (!analyzer.inTag())
                {
                    offsetToRemove = lastPartitionEnd;
                    lastPartitionEnd = 0;
                }

                // Step 6
                if (offsetToRemove > 0)
                {
                    document.replace(0, offsetToRemove, "");
                }
            } catch (BadLocationException e)
            {
                TLCUIActivator.logError("Error removing text or retrieving text from the parser's document."
                        + "This is a bug.", e);
            }
        }
    }

    /**
     * Constructs the parser
     * @param name
     * @param prio
     * @param isTraceExplorer TODO
     */
    public TagBasedTLCOutputIncrementalParser(String name, int prio, boolean isTraceExplorer)
    {
        // create the document
        document = new Document();

        this.analyzer = new TagBasedTLCAnalyzer(document);
        this.source = new CachingTLCOutputSource(name, prio);

        // set up the partitioner
        FastPartitioner partitioner = new FastPartitioner(new TagBasedTLCOutputTokenScanner(),
                TagBasedTLCOutputTokenScanner.CONTENT_TYPES);
        partitioner.connect(document);
        document.setDocumentPartitioner(partitioner);
        

        // now register the listener, responsible for evaluating the partitioning information
        document.addDocumentPartitioningListener(new TLCOutputPartitionChangeListener());

        /*
         *  Register the process source
         *  
         *  There are two different source registries, one for trace exploration
         *  and one for model checking. The source must be added to the
         *  appropriate registry.
         */
        if (isTraceExplorer)
        {
            TLCOutputSourceRegistry.getTraceExploreSourceRegistry().addTLCOutputSource(this.source);
        } else
        {
            TLCOutputSourceRegistry.getModelCheckSourceRegistry().addTLCOutputSource(this.source);
        }
    }

    /**
     * add the increment
     * 
     * The argument should be a relatively short string, i.e. no more
     * than what TLC prints out in a single instant.
     * 
     * It is also better if when at least one TLC end tag is part
     * of the string passed to this method, the string terminates with
     * a TLC end tag.
     * 
     * @param text
     * @throws BadLocationException
     */
    public void addIncrement(String text) throws BadLocationException
    {
		// don't waste time, skip empty or new lines
		if (text == null || text.length() == 0 || text.equals("\n")) {
			return;
		} else if(text.charAt(text.length() - 1) != 10) { // 10 ascii for '\n'
			throw new BadLocationException("Input does not end with newline");
			//text = text + (char) 10;
		}

		document.replace(document.getLength(), 0, text);
    }

	IDocument getDocument() {
		return document;
	}
	
	TagBasedTLCAnalyzer getTagAnalyzer() {
		return analyzer;
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
