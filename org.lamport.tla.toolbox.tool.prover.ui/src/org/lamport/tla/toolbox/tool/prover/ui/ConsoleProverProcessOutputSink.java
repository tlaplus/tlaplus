package org.lamport.tla.toolbox.tool.prover.ui;

import java.io.IOException;

import org.eclipse.ui.console.IOConsoleOutputStream;
import org.eclipse.ui.console.MessageConsole;
import org.lamport.tla.toolbox.tool.prover.output.IProverProcessOutputSink;

/**
 * This output sink sends text to the TLAPM console.
 * 
 * This class receives output by registering at the extension point
 * org.lamport.tla.toolbox.tool.prover.processOutputSink.
 * 
 * @author Daniel Ricketts
 *
 */
public class ConsoleProverProcessOutputSink implements IProverProcessOutputSink
{

    private MessageConsole console;
    private IOConsoleOutputStream outputStream;

    public ConsoleProverProcessOutputSink()
    {
        this.console = TLAPMConsoleFactory.getTLAPMConsole();
        this.outputStream = this.console.newOutputStream();
    }

    /**
     * Sends text to the TLAPM console.
     */
    public void appendText(String text)
    {
        try
        {
            this.outputStream.write(text.getBytes());
        } catch (IOException e)
        {
            ProverUIActivator.logError("Error printing a console message: >" + text + "<", e);
        }
    }

    public void initializeSink(String processName, int sinkType)
    {
        // TODO Auto-generated method stub

    }

    public void processFinished()
    {
        // TODO Auto-generated method stub

    }

}
