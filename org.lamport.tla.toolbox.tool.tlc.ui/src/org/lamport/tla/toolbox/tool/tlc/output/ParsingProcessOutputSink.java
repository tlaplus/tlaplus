package org.lamport.tla.toolbox.tool.tlc.output;

import java.util.Vector;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.TypedRegion;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

/**
 * Parses data coming from the process
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParsingProcessOutputSink implements IProcessOutputSink
{
    private IDocument document;
    private int lastPartitionEnd;
    private Vector typedRegions;
    private Vector userRegions;
    private String processName;
    private CoverageAnalyzer analyzer = new CoverageAnalyzer(true);

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#appendText(java.lang.String)
     */
    public void appendText(String text)
    {
        try
        {
            document.replace(document.getLength(), 0, text);
            IDocumentPartitioner partitioner = document.getDocumentPartitioner();

            int startOfUnpartitionedText = Math.min(document.getLength(), lastPartitionEnd);

            System.out.println("Parsing from " + startOfUnpartitionedText + " to " + document.getLength());
            ITypedRegion[] regions = partitioner.computePartitioning(startOfUnpartitionedText, document.getLength());

            // iterate partitions from the end to the front, and looking for the last
            // non-default (user-output) partition
            Vector userTempPartitions = new Vector();
            for (int i = 0; i < regions.length; i++)
            {
                // looking for non-default content type
                if (!LogPartitionTokenScanner.DEFAULT_CONTENT_TYPE.equals(regions[i].getType()))
                {
                    // typed partition detected
                    int currentPartitionEnd = regions[i].getOffset() + regions[i].getLength();
                    if (currentPartitionEnd > lastPartitionEnd)
                    {
                        lastPartitionEnd = currentPartitionEnd;
                    }

                    
                    if (LogPartitionTokenScanner.COVERAGE_START.equals(regions[i].getType()))
                    {
                        // just add the partition to the alayzer 
                        analyzer.addCoverageStart(regions[i]);
                    } 
                    
                    
                    if (LogPartitionTokenScanner.COVERAGE_END.equals(regions[i].getType())) 
                    {
                        // if the coverage end is detected, everything between the start and 
                        // the end are not user partitions, but 
                        // coverage information
                        analyzer.addCoverageEnd(regions[i]);
                        
                        ITypedRegion coverage = analyzer.getCoverageRegion();
                        // add the typed coverage region
                        typedRegions.add(coverage);
                        // debug print
                        printPartition(coverage, document);
                        // re-initialize the user partitions
                        userTempPartitions = new Vector();
                    } else
                    {

                        typedRegions.add(regions[i]);

                        // user partitions found
                        if (userTempPartitions.size() > 1)
                        {
                            int startLine = document.getLineOfOffset(((TypedRegion) userTempPartitions.elementAt(0))
                                    .getOffset());
                            int endLine = document.getLineOfOffset(((TypedRegion) userTempPartitions
                                    .elementAt(userTempPartitions.size() - 1)).getOffset());
                            ITypedRegion mergedPartition = LogPartitionTokenScanner
                                    .mergePartitions((ITypedRegion[]) userTempPartitions
                                            .toArray(new TypedRegion[userTempPartitions.size()]));
                            System.out.println("Merged " + userTempPartitions.size() + " user partitions. Lines from "
                                    + startLine + " to " + endLine + ".");
                            this.userRegions.add(mergedPartition);
                            printPartition(mergedPartition, document);
                            
                            // re-initialize the user partitions                            
                            userTempPartitions = new Vector();
                        }
                    }
                } else
                {
                    // if the partition has no type (default one), it is the user partition...
                    userTempPartitions.add(regions[i]);
                }
            }

        } catch (BadLocationException e)
        {
            TLCUIActivator.logError("Error parsing the TLC output stream for " + this.processName, e);
        }
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#initializeSink(java.lang.String, int)
     */
    public void initializeSink(String processName, int sinkType)
    {

        this.processName = processName;
        this.document = new Document();
        this.typedRegions = new Vector();
        this.userRegions = new Vector();

        if (this.document != null)
        {
            FastPartitioner partitioner = new FastPartitioner(new LogPartitionTokenScanner(),
                    LogPartitionTokenScanner.CONTENT_TYPES);
            partitioner.connect(document);
            this.document.setDocumentPartitioner(partitioner);
        }

    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#processFinished()
     */
    public void processFinished()
    {

    }

    /**
     * 
     * 
     */
    private void printPartitions()
    {
        System.out.println("TypedRegions:" + typedRegions.size());
        for (int i = 0; i < typedRegions.size(); i++)
        {
            TypedRegion region = (TypedRegion) typedRegions.get(i);
            printPartition(region, document);
        }
    }

    public static void printPartition(ITypedRegion region, IDocument document)
    {
        if (region == null)
        {
            return;
        }
        try
        {
            int offset = region.getOffset();
            int printLength = Math.min(region.getLength(), 50);
            String type = region.getType();
            StringBuffer messageBuffer = new StringBuffer();
            String location = "[" + region.getOffset() + ":" + region.getLength() + "]";
            String head = document.get(offset, printLength);
            if (LogPartitionTokenScanner.COVERAGE.equals(type))
            {
                messageBuffer.append("Coverage " + location + ": >" + head + "< ...");
            } else if (LogPartitionTokenScanner.PROGRESS.equals(type))
            {
                messageBuffer.append("Progress " + location + ": >" + head + "< ...");
            } else if (LogPartitionTokenScanner.INIT_START.equals(type))
            {
                messageBuffer.append("Init start " + location + ": >" + head + "< ...");
            } else if (LogPartitionTokenScanner.INIT_END.equals(type))
            {
                messageBuffer.append("Init end " + location + ": >" + head + "< ...");
            } else if (LogPartitionTokenScanner.OUTPUT.equals(type))
            {
                String tail = document.get(offset + region.getLength() - printLength, printLength);
                messageBuffer.append("User " + location + ": >" + head + "< .. >" + tail + "<");
            } else
            {
                messageBuffer.append("UNKNOWN " + location + ": >" + head + "< ...");
            }

            System.out.println(messageBuffer.toString());

        } catch (BadLocationException e)
        {
            e.printStackTrace();
        }

    }
}
