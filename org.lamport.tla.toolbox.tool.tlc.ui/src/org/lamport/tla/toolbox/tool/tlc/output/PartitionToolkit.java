package org.lamport.tla.toolbox.tool.tlc.output;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.TypedRegion;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputTokenScanner;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCRegion;
import org.lamport.tla.toolbox.tool.tlc.output.source.TagBasedTLCOutputTokenScanner;

/**
 * A toolkit with helper methods
 * @author Simon Zambrovski
 * @version $Id$
 */
public class PartitionToolkit
{
    public static final int TYPE_UNKNOWN = -1;
    public static final int TYPE_USER_OUTPUT = 1;
    public static final int TYPE_INIT_END = 2;
    public static final int TYPE_INIT_START = 3;
    public static final int TYPE_PROGRESS = 4;
    public static final int TYPE_COVERAGE = 5;
    public static final int TYPE_TAG = 6;

    /**
     * Merges an array of partitions of the same type to one partition of this type
     * @param regions array of partitions of the same type, which MUST be intervals of document following 
     * each other continuously ([i, i+k], [i+k, i+k+l], [i+k+l, i+k+l+n], etc)...    
     * @return one partition starting as the first element and ending as the last in the array, 
     * or <code>null</code> on any error
     */
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

    /**
     * Prints partition information
     * @param region
     * @param document
     */
    public static void printPartition(ITypedRegion region, IDocument document)
    {
        if (region == null)
        {
            return;
        }

        try
        {
            StringBuffer messageBuffer = new StringBuffer();
            String location = "[" + region.getOffset() + ":" + region.getLength() + "]";

            if (region instanceof TLCRegion)
            {
                TLCRegion tlcRegion = (TLCRegion) region;
                messageBuffer.append("TLC:" + tlcRegion.getMessageCode() + " " + tlcRegion.getSeverity() + " "
                        + location);
            } else
            {
                int offset = region.getOffset();
                int printLength = Math.min(region.getLength(), 50);
                String type = region.getType();
                String head = document.get(offset, printLength);
                if (TLCOutputTokenScanner.COVERAGE.equals(type))
                {
                    messageBuffer.append("Coverage " + location + ": >" + head + "< ...");
                } else if (TLCOutputTokenScanner.PROGRESS.equals(type))
                {
                    messageBuffer.append("Progress " + location + ": >" + head + "< ...");
                } else if (TLCOutputTokenScanner.INIT_START.equals(type))
                {
                    messageBuffer.append("Init start " + location + ": >" + head + "< ...");
                } else if (TLCOutputTokenScanner.INIT_END.equals(type))
                {
                    messageBuffer.append("Init end " + location + ": >" + head + "< ...");
                } else if (TLCOutputTokenScanner.OUTPUT.equals(type))
                {
                    String tail = document.get(offset + region.getLength() - printLength, printLength);
                    messageBuffer.append("User " + location + ": >" + head + "< .. >" + tail + "<");
                } else
                {
                    messageBuffer.append("UNKNOWN " + location + ": >" + head + "< ...");
                }
            }
            System.out.println(messageBuffer.toString());

        } catch (BadLocationException e)
        {
            e.printStackTrace();
        }

    }

    public static int getRegionTypeAsInt(ITypedRegion region)
    {
        Assert.isNotNull(region);
        String type = region.getType();
        if (TLCOutputTokenScanner.COVERAGE.equals(type))
        {
            return TYPE_COVERAGE;
        } else if (TLCOutputTokenScanner.PROGRESS.equals(type))
        {
            return TYPE_PROGRESS;
        } else if (TLCOutputTokenScanner.INIT_START.equals(type))
        {
            return TYPE_INIT_START;
        } else if (TLCOutputTokenScanner.INIT_END.equals(type))
        {
            return TYPE_INIT_END;
        } else if (TLCOutputTokenScanner.OUTPUT.equals(type))
        {
            return TYPE_USER_OUTPUT;
        } else if (TagBasedTLCOutputTokenScanner.TAG.equals(type))
        {
            return TYPE_TAG;
        }else
        {
            return TYPE_UNKNOWN;
        }

    }
}
