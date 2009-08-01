package org.lamport.tla.toolbox.tool.tlc.output;

import org.eclipse.jface.text.BadLocationException;
import org.lamport.tla.toolbox.tool.tlc.output.source.ITLCOutputSource;
import org.lamport.tla.toolbox.tool.tlc.output.source.TagBasedTLCOutputIncrementalParser;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

/**
 * A sink that uses TLC output parser for parsing
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParsingTLCOutputSink implements IProcessOutputSink
{
    // private TLCOutputIncrementalParser parser;    
    private TagBasedTLCOutputIncrementalParser parser;

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#appendText(java.lang.String)
     */
    public void appendText(String text)
    {
        try
        {
            parser.addIncrement(text);

        } catch (BadLocationException e)
        {
            TLCUIActivator.logError("Error parsing the TLC output stream for "
                    + this.parser.getSource().getSourceName(), e);
        }
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#initializeSink(java.lang.String, int)
     */
    public void initializeSink(String processName, int sinkType)
    {
        // parser = new TLCOutputIncrementalParser(processName, ITLCOutputSource.PRIO_HIGH);
        parser = new TagBasedTLCOutputIncrementalParser(processName, ITLCOutputSource.PRIO_HIGH);
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#processFinished()
     */
    public void processFinished()
    {
        this.parser.done();
    }

}
