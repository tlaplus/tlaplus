package org.lamport.tla.toolbox.tool.tlc.ui.output;

import java.util.Vector;

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

            ITypedRegion[] regions = partitioner.computePartitioning(startOfUnpartitionedText, document.getLength());
            System.out.print("Found " + regions.length + " partitions, ");
            
            // iterate partitions from the end to the front, and looking for the last non-default (user-output)
            // partition
            int j = 0;
            for (int i = regions.length - 1; i >= 0; i--)
            {
                if (regions[i] != null && !LogPartitionTokenScanner.DEFAULT_CONTENT_TYPE.equals(regions[i].getType()))
                {

                    int currentPartitionEnd = regions[i].getOffset() + regions[i].getLength();
                    if (currentPartitionEnd > lastPartitionEnd)
                    {
                        lastPartitionEnd = currentPartitionEnd;
                    }
                    typedRegions.add(regions[i]);
                    j++;
                }
            }
            
            System.out.print(" " + j + " of them non-user\n");
            

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

    public static void printPartition(TypedRegion region, IDocument document)
    {
        try
        {
            int offset = region.getOffset();
            int length = region.getLength();
            String type = region.getType();

            String text = document.get(offset, length);
            if (LogPartitionTokenScanner.COVERAGE.equals(type))
            {
                System.out.println("Coverage: " + text);
            } else if (LogPartitionTokenScanner.PROGRESS.equals(type))
            {
                System.out.println("Progress: " + text);
            } else if (LogPartitionTokenScanner.INIT_START.equals(type))
            {
                System.out.println("Init start: " + text);
            } else if (LogPartitionTokenScanner.INIT_END.equals(type))
            {
                System.out.println("Init end: " + text);
            }
        } catch (BadLocationException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

    }
}
