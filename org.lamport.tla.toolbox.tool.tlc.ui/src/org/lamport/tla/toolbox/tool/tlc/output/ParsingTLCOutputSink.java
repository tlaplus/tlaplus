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
	private String buffer = "";

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#appendText(java.lang.String)
     */
    public synchronized void appendText(String text)
    {
    	// parser only handles complete lines, thus we buffer incomplete
    	// lines here (speeds up parsing too)

    	// a) prepend the previous text
    	text = buffer + text;
    	buffer = "";
    	
    	final int lastLineBreak = text.lastIndexOf(10);
    	final int length = text.length();
    	// b) complete lines are directly fed to the parser
		if (lastLineBreak == length) {
    		addIncrement(text);
    	// c) Feed all complete lines of a multi-line input
    	} else {
    		final String substring = text.substring(0, lastLineBreak + 1);
    		addIncrement(substring);
    		// d) suffix is saved for next invocation or done()
    		buffer = text.substring(lastLineBreak + 1);
    	}
    }

    private void addIncrement(final String input) {
		try {
			parser.addIncrement(input);
		} catch (BadLocationException e) {
            TLCUIActivator.logError("Error parsing the TLC output stream for "
                    + this.parser.getSource().getTLCOutputName(), e);
		}
    }
    
    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#initializeSink(java.lang.String, int)
     */
    public void initializeSink(String processName, int sinkType)
    {
        boolean isTraceExploration = sinkType == IProcessOutputSink.TYPE_TRACE_EXPLORE;
        // parser = new TLCOutputIncrementalParser(processName, ITLCOutputSource.PRIO_HIGH);
        parser = new TagBasedTLCOutputIncrementalParser(processName, ITLCOutputSource.PRIO_HIGH, isTraceExploration);
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#processFinished()
     */
    public void processFinished()
    {
    	// feed the rest of the buffer to the parser
    	if(buffer.length() > 0) {
    		addIncrement(buffer);
    	}
        this.parser.done();
    }
}
