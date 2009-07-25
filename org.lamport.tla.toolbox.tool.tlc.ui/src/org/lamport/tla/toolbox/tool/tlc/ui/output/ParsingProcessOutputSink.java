package org.lamport.tla.toolbox.tool.tlc.ui.output;

import java.util.Vector;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.TypedRegion;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink;

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
                if (!LogPartitionTokenScanner.DEFAULT_CONTENT_TYPE.equals(regions[i].getType()))
                {
                    int currentPartitionEnd = regions[i].getOffset() + regions[i].getLength();
                    if (currentPartitionEnd > lastPartitionEnd)
                    {
                        lastPartitionEnd = currentPartitionEnd;
                    }
                    typedRegions.add(regions[i]);

                    // user partitions found
                    if (userTempPartitions.size() > 1)
                    {
                        int startLine = document.getLineOfOffset(((TypedRegion)userTempPartitions.elementAt(0)).getOffset());
                        int endLine = document.getLineOfOffset(((TypedRegion)userTempPartitions.elementAt(userTempPartitions.size() - 1)).getOffset());
                        ITypedRegion mergedPartition = mergePartitions((ITypedRegion[]) userTempPartitions
                                .toArray(new TypedRegion[userTempPartitions.size()]));
                        System.out.println("Merged " + userTempPartitions.size() + " user partitions. Lines from " + startLine + " to " + endLine + ".");
                        this.userRegions.add(mergedPartition);
                        printPartition(mergedPartition, document);
                        userTempPartitions = new Vector();
                    }

                    // don't print the detected typed partitions
                    // printPartition(regions[i], document);
                } else
                {
                    userTempPartitions.add(regions[i]);
                }
            }

        } catch (BadLocationException e)
        {
            e.printStackTrace();
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

    public static ITypedRegion mergePartitions(ITypedRegion[] regions)
    {
        Assert.isNotNull(regions);
        if (regions.length == 0)
        {
            return null;
        }
        String type = null;
        int offset = -1;
        int length = 0;
        int matcher = -1;

        for (int i = 0; i < regions.length; i++)
        {
            if (type == null)
            {
                type = regions[i].getType();
            } else
            {
                if (!type.equals(regions[i].getType()))
                {
                    return null;
                }
            }
            if (offset == -1)
            {
                offset = regions[i].getOffset();

            } else
            {
                if (regions[i].getOffset() != matcher)
                {
                    return null;
                }
            }

            matcher = regions[i].getOffset() + regions[i].getLength();
            length += regions[i].getLength();

        }
        return new TypedRegion(offset, length, type);
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
