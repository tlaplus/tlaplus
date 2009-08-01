package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.Stack;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITypedRegion;

/**
 * Coverage information processor
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TagBasedTLCAnalyzer
{
    private static final String TAG = TagBasedTLCOutputTokenScanner.TAG;
    private TLCRegion taggedRegion = null;
    private Stack stack;
    private final IDocument document;

    /**
     * Constructs the analyzer
     * @param failOnError a flag indicating that the analyzer will fail if the start and end 
     * are not set in the interleaving manner. 
     */
    public TagBasedTLCAnalyzer(IDocument document)
    {
        this.document = document;
        stack = new Stack();
    }

    /**
     * Add start of coverage
     * @param start
     */
    public void addTagStart(ITypedRegion start)
    {
        synchronized (stack)
        {
            stack.push(start);
        }
    }

    /**
     * Add the end of coverage
     * @param end
     */
    public void addTagEnd(ITypedRegion end)
    {
        synchronized (stack)
        {
            stack.push(end);
            processTag();
        }
    }

    /**
     * Process the calculation of the coverage region
     */
    protected synchronized void processTag()
    {
        Assert.isTrue(!stack.isEmpty(), "Bug. Empty stack, end tag expected");
        ITypedRegion end = (ITypedRegion) stack.pop();
        
        Assert.isTrue(!stack.isEmpty(), "Bug. Empty stack, start tag expected"); 
        ITypedRegion start = (ITypedRegion) stack.pop();

        int length = end.getOffset() - start.getLength() - start.getOffset();
        this.taggedRegion = new TLCRegion(start.getOffset() + start.getLength(), length - 1 , TAG);
        this.taggedRegion.setMessageCode(getMessageCode(start));
        this.taggedRegion.setSeverity(getSeverity(start));
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
    private int getMessageCode(ITypedRegion region)
    {
        try
        {
            String text = document.get(region.getOffset(), region.getLength() );
            int index = text.indexOf(":");
            String number = text.substring(text.indexOf(" ") + 1, index);
            return Integer.parseInt(number);
        } catch (BadLocationException e)
        {
            e.printStackTrace();
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
            String text = document.get(region.getOffset(), region.getLength() );
            int index = text.indexOf(":");
            String number = text.substring(index + 1, text.indexOf(" ", index));
            return Integer.parseInt(number);
        } catch (BadLocationException e)
        {
            e.printStackTrace();
        }
        return -1;
    } 

}
