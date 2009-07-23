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
            // System.out.print("Found " + regions.length + " partitions\n");

            // iterate partitions from the end to the front, and looking for the last non-default (user-output)
            // partition
            int j = 0;
            StringBuffer buffer = new StringBuffer(">");
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

                    int offset;
                    if (j == 0)
                    {
                        offset = 0;

                    } else
                    {
                        offset = ((TypedRegion) typedRegions.get(j)).getOffset()
                                + ((TypedRegion) typedRegions.get(j)).getLength();
                    }
                    int length = regions[i].getOffset();
                    j++;

                    if (buffer.length() > 1)
                    {
                        buffer.append("<");
                        String location = "[" + offset + ":" + length + "]";
                        System.out.println("User " + location + ":" + buffer.toString());
                        buffer = new StringBuffer(">");
                    }

                    printPartition(regions[i], document);
                } else
                {

                    buffer.append(document.get(regions[i].getOffset(), regions[i].getLength()));
                }
            }

            if (regions.length > 9) 
            {
                TypedRegion[] merge = new TypedRegion[10];
                System.arraycopy(regions, regions.length - 10, merge, 0, merge.length);
                printPartition(mergePartitions(merge), document);
            }

            // System.out.print(" " + j + " of them non-user\n");

        } catch (BadLocationException e)
        {
            // 
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
            int length = Math.min(region.getLength(), 50);
            String type = region.getType();

            String location = "[" + region.getOffset() + ":" + region.getLength() + "]";
            String text = document.get(offset, length);
            if (LogPartitionTokenScanner.COVERAGE.equals(type))
            {
                System.out.println("Coverage " + location + ":" + text);
            } else if (LogPartitionTokenScanner.PROGRESS.equals(type))
            {
                System.out.println("Progress " + location + ":" + text);
            } else if (LogPartitionTokenScanner.INIT_START.equals(type))
            {
                System.out.println("Init start " + location + ":" + text);
            } else if (LogPartitionTokenScanner.INIT_END.equals(type))
            {
                System.out.println("Init end " + location + ":" + text);
            } else if (LogPartitionTokenScanner.OUTPUT.equals(type))
            {
                System.out.println("User " + location + ":" + text);
            } else
            {
                System.out.println("UNKNOWN " + location + ":" + text);
            }
        } catch (BadLocationException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

    }
}
