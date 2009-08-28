package org.lamport.tla.toolbox.tool.tlc.output;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.TypedRegion;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCRegion;
import org.lamport.tla.toolbox.tool.tlc.output.source.TagBasedTLCOutputTokenScanner;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

/**
 * A toolkit with helper methods
 * @author Simon Zambrovski
 * @version $Id$
 */
public class PartitionToolkit
{
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
                int printLength = Math.min(region.getLength(), 255);

                String type = region.getType();
                Assert.isTrue(type.equals(TagBasedTLCOutputTokenScanner.DEFAULT_CONTENT_TYPE));

                String head = document.get(offset, printLength);
                messageBuffer.append("OUTPUT:" + location + ": >" + head + "< ...");
            }

            TLCUIActivator.logDebug(messageBuffer.toString());

        } catch (BadLocationException e)
        {
            TLCUIActivator.logError("Error printing partition", e);
        }

    }
}
