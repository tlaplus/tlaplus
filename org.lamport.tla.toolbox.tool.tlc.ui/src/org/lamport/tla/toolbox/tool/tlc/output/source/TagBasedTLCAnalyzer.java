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

    // @!@!@STARTMSG 2219:0 @!@!@
    public static final int OPEN_TAG_LENGTH = 28;
    // @!@!@ENDMSG 2219 @!@!@
    public static final int CLOSE_TAG_LENGTH = 24;
    
    
    
    
    
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
        // Assert.isTrue(inTag() && !inTag() == !hasUserPartitions(),
        // "Found user partitions which have not been removed. This is a bug.");

        ITypedRegion userRegion = getUserRegion();
        if (userRegion != null)
        {
            stack.push(userRegion);
        }
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
        ITypedRegion userRegion = getUserRegion();
        if (userRegion != null)
        {
            stack.push(userRegion);
        }
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

    public boolean inTag()
    {
        return !stack.isEmpty();
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

        // find content until matching start tag on the stack
        // it is assumed that it is:
        // User, TLC-Tag, Start
        // User, Start
        // TLC-Tag, Start
        // TLC-Tag, User, Start
        // currently only this patterns are supported!
        // the Start tag is always the last
        // if there is a TLCTag on the stack, the content is already captured by it...
        ITypedRegion[] stackContent = getFindStart(messageCode);

        TLCRegion start = (TLCRegion) stackContent[stackContent.length - 1];

        int length = end.getOffset() - start.getLength() - start.getOffset();
        int offset = start.getOffset() + start.getLength();

        TLCRegion region;
        if (stackContent.length > 1)
        {
            region = new TLCRegionContainer(offset, length - 1);
            Vector regions = new Vector();
            for (int i = 0; i < stackContent.length - 1; i++)
            {
                regions.add(stackContent[i]);
                if (stackContent[i] instanceof TLCRegion)
                {
                    if (offset == stackContent[i].getOffset() - OPEN_TAG_LENGTH)
                    {
                        // the current tag and the child tag starts with the same offset
                        // it is either TLC-TAG, USer, Start case
                        // or TLC-TAG, Start case
                        if (length - CLOSE_TAG_LENGTH == stackContent[i].getLength())
                        {
                            // the child tag covers the same region as the current tag
                            // current tag is a container without a message
                            length = -1;
                            offset = -1;
                        } else
                        {
                            int shift = OPEN_TAG_LENGTH + stackContent[i].getLength();
                            offset = offset + shift;
                            length = length - shift;
                        }
                    } else if (offset + length - CLOSE_TAG_LENGTH == stackContent[i].getOffset() + stackContent[i].getLength())
                    {
                        int shift = stackContent[i].getLength();
                        length = length - shift;
                    } else
                    {
                        // NOT SUPPORTED
                        System.out.println("JJ");
                    }
                }
            }
            ((TLCRegionContainer) region).setSubRegions(regions);
        } else
        {
            region = new TLCRegion(offset, length - 1);
        }
        region.setMessageCode(start.getMessageCode());
        region.setSeverity(start.getSeverity());

        if (inTag())
        {
            stack.push(region);
        } else
        {
            this.taggedRegion = region;
        }
    }

    /**
     * Returns array of elements from top of the stack with start as the last element (call pop until the start is found) 
     * @param code
     * @return
     */
    private ITypedRegion[] getFindStart(int code)
    {
        Assert.isTrue(!stack.isEmpty(), "Bug. Empty stack, start tag expected");

        Vector elements = new Vector();
        while (!stack.isEmpty())
        {
            ITypedRegion region = (ITypedRegion) stack.pop();
            elements.add(region);
            if (TagBasedTLCOutputTokenScanner.TAG_OPEN.equals(region.getType()))
            {
                TLCRegion startRegion = (TLCRegion) region;
                Assert.isTrue(startRegion.getMessageCode() == code, "Found a non-matching start. This is a bug.");
                // found a match
                break;
            } else
            {
                // not a start tag
                // but something else, e.G. user partition

            }
        }

        return (ITypedRegion[]) elements.toArray(new ITypedRegion[elements.size()]);
    }

    /**
     * @return
     */
    public ITypedRegion getUserRegion()
    {
        if (hasUserPartitions())
        {
            ITypedRegion region = PartitionToolkit.mergePartitions((ITypedRegion[]) userOutput
                    .toArray(new TypedRegion[userOutput.size()]));
            // re-initialize the user partitions
            resetUserPartitions();
            return region;
        } else
        {
            return null;
        }
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
