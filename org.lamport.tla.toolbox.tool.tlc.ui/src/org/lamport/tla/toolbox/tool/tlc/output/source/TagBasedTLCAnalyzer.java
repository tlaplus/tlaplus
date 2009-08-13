package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.Stack;
import java.util.Vector;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.TypedRegion;
import org.lamport.tla.toolbox.tool.tlc.output.PartitionToolkit;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

/**
 * Message processor, detects message code, severity and the message body from the TLC tags
 * <br>Currently, only one level tags are supported (container tag with one user input tag contained)
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TagBasedTLCAnalyzer
{

    private static final int START = 1;
    private static final int END = 2;

    private TLCRegion taggedRegion = null;

    private final IDocument document;
    private Stack stack;
    private Vector userOutput;

    /**
     * Constructs the analyzer
     * @param failOnError a flag indicating that the analyzer will fail if the start and end 
     * are not set in the interleaving manner. 
     */
    public TagBasedTLCAnalyzer(IDocument document)
    {
        this.document = document;
        stack = new Stack();
        resetUserPartitions();
    }

    /**
     * Add start of coverage
     * @param start
     */
    public void addTagStart(ITypedRegion start)
    {
        TLCRegion startRegion = new TLCRegion(start.getOffset(), start.getLength(), start.getType());
        startRegion.setMessageCode(getMessageCode(start, START));
        startRegion.setSeverity(getSeverity(start));
        // add start to stack
        stack.push(startRegion);
    }

    /**
     * Add the end of coverage
     * @param end
     */
    public void addTagEnd(ITypedRegion end)
    {
        processTag(end);
    }

    /**
     * 
     * @param iTypedRegion
     */
    public void addUserRegion(ITypedRegion userRegion)
    {
        userOutput.add(userRegion);
    }

    /**
     * Retrieves if user partitions are present 
     */
    public boolean hasUserPartitions()
    {
        return (userOutput.size() > 1);
    }

    /**
     * 
     */
    public void resetUserPartitions()
    {
        userOutput = new Vector();
    }

    /**
     * Process the calculation of the coverage region
     */
    private void processTag(ITypedRegion end)
    {
        // read the message code of the end tag
        int messageCode = getMessageCode(end, END);

        // find matching start tag on the stack
        TLCRegion start = getMatchingStart(messageCode);

        int length = end.getOffset() - start.getLength() - start.getOffset();
        int offset = start.getOffset() + start.getLength();

        if (hasUserPartitions())
        {
            this.taggedRegion = new TLCRegionContainer(offset, length - 1);
            Vector regions = new Vector();
            regions.add(getUserRegion());
            ((TLCRegionContainer)this.taggedRegion).setSubRegions(regions);

        } else
        {
            this.taggedRegion = new TLCRegion(offset, length - 1);
        }
        this.taggedRegion.setMessageCode(start.getMessageCode());
        this.taggedRegion.setSeverity(start.getSeverity());
    }

    /**
     * 
     * @param code
     * @return
     */
    private TLCRegion getMatchingStart(int code)
    {
        Assert.isTrue(!stack.isEmpty(), "Bug. Empty stack, start tag expected");
        
        while (!stack.isEmpty())
        {
            ITypedRegion region = (ITypedRegion) stack.pop();
            if (TagBasedTLCOutputTokenScanner.TAG_OPEN.equals(region.getType()))
            {
                TLCRegion startRegion = (TLCRegion) region;
                if (startRegion.getMessageCode() == code) 
                {
                    // found a match
                    return startRegion;
                } else 
                {
                    // found a non-matching start. this is a bug
                }
            } else 
            {
                // not a start tag 
            }
        }
        
        
        return null;
    }

    /**
     * @return
     */
    public ITypedRegion getUserRegion()
    {
        // try
        // {
        // int startLine = document.getLineOfOffset(((TypedRegion) userOutput.elementAt(0)).getOffset());
        // int endLine = document.getLineOfOffset(((TypedRegion) userOutput.elementAt(userOutput.size() - 1))
        // .getOffset());
        //
        // TLCUIActivator.logDebug("Merged " + userOutput.size() + " user partitions. Lines from " + startLine
        // + " to " + endLine + ".");
        // } catch (BadLocationException e)
        // {
        // TLCUIActivator.logError("Error retrieven region", e);
        // }

        ITypedRegion region = PartitionToolkit.mergePartitions((ITypedRegion[]) userOutput
                .toArray(new TypedRegion[userOutput.size()]));
        // re-initialize the user partitions
        resetUserPartitions();
        return region;
    }

    /**
     * Retrieves last detected coverage region, or null if no coverage information were available
     * @return
     */
    public TLCRegion getTaggedRegion()
    {
        return this.taggedRegion;
    }

    /**
     * Retrieves the message type
     * @param region
     * @return
     */
    private int getMessageCode(ITypedRegion region, int type)
    {
        try
        {
            String text = document.get(region.getOffset(), region.getLength());
            int index;
            String number;
            switch (type) {
            case START:
                index = text.indexOf(":");
                break;
            case END:
                index = text.lastIndexOf(" ");
                break;
            default:
                // make compiler happy
                index = -1;
                break;
            }
            if (index == -1) 
            {
                Assert.isTrue(index != -1, "Could not read message code");
            }
            
            number = text.substring(text.indexOf(" ") + 1, index);
            return Integer.parseInt(number);
        } catch (BadLocationException e)
        {
            TLCUIActivator.logError("Error retrieving the TLC message code", e);
        }
        return -1;
    }

    /**
     * Retrieves the message severity
     * @param region
     * @return
     */
    private int getSeverity(ITypedRegion region)
    {
        try
        {
            String text = document.get(region.getOffset(), region.getLength());
            int index = text.indexOf(":");
            String number = text.substring(index + 1, text.indexOf(" ", index));
            return Integer.parseInt(number);
        } catch (BadLocationException e)
        {
            TLCUIActivator.logError("Error retrieving the TLC message severity", e);
        }
        return -1;
    }

}
