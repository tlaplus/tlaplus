package org.lamport.tla.toolbox.tool.tlc.output;

import java.util.Collections;
import java.util.Vector;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.TypedRegion;
import org.eclipse.jface.text.rules.FastPartitioner;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCOutputHolder
{
    private IDocument document;
    private int lastPartitionEnd;
    private Vector typedRegions;

    /**
     * 
     */
    public TLCOutputHolder()
    {
        document = new Document();
        typedRegions = new Vector();

        if (document != null)
        {
            FastPartitioner partitioner = new FastPartitioner(new LogPartitionTokenScanner(),
                    LogPartitionTokenScanner.CONTENT_TYPES);
            partitioner.connect(document);
            document.setDocumentPartitioner(partitioner);
        }

    }

    /**
     * Appends the text to the document
     * @param text
     */
    public void append(String text)
    {
        try
        {
            document.replace(document.getLength(), 0, text);

            IDocumentPartitioner partitioner = document.getDocumentPartitioner();

            int startOfUnpartitionedText = Math.min(document.getLength(), lastPartitionEnd);

            ITypedRegion[] regions = partitioner.computePartitioning(startOfUnpartitionedText, document.getLength());
            
            // iterate partitions from the end to the front, and looking for the last 
            ITypedRegion lastPartition = regions[regions.length - 1];
            if (lastPartition != null)
            {
                lastPartitionEnd = lastPartition.getOffset() + lastPartition.getLength();
            }

            Collections.addAll(typedRegions, regions);

            printPartitions();

        } catch (BadLocationException e)
        {
            // 
            e.printStackTrace();
        }
    }

    /**
     * 
     * 
     */
    private void printPartitions()
    {
        try
        {
            System.out.println("TypedRegions:" + typedRegions.size());
            for (int i = 0; i < typedRegions.size(); i++)
            {
                TypedRegion region = (TypedRegion) typedRegions.get(i);
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
            }

        } catch (BadLocationException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

    }

}
