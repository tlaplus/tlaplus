package org.lamport.tla.toolbox.tool.tlc.output;

import java.io.IOException;

import org.eclipse.ui.console.IOConsoleOutputStream;
import org.eclipse.ui.console.MessageConsole;
import org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.console.ConsoleFactory;

/**
 * A sink writing to a console
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ConsoleProcessOutputSink implements IProcessOutputSink
{

    private MessageConsole console;
    private IOConsoleOutputStream outputStream;

    public ConsoleProcessOutputSink()
    {
        this.console = ConsoleFactory.getTLCConsole();
        this.outputStream = this.console.newOutputStream();
        // this.console.activate();
    }

    public synchronized void appendText(String text)
    {

        try
        {
            this.outputStream.write(text.getBytes());
        } catch (IOException e)
        {
            TLCUIActivator.getDefault().logError("Error printing a console message: >" + text + "<", e);
        }
    }

    public void initializeSink(String processName, int sinkType)
    {

    }

    public void processFinished()
    {

    }

    /**
     * Initializes the console and shows the view 
     */
    protected void initConsole()
    {

    }

}
