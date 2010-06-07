package org.lamport.tla.toolbox.tool.prover.output.internal;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.IStreamListener;
import org.eclipse.debug.core.model.IStreamMonitor;
import org.lamport.tla.toolbox.tool.prover.output.IProverProcessOutputSink;
import org.lamport.tla.toolbox.tool.prover.ui.ConsoleProverProcessOutputSink;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.output.ParsingProverProcessOutputSink;

/**
 * A listener that broadcasts streams to a {@link ConsoleProverProcessOutputSink}
 * and a {@link ParsingProverProcessOutputSink}.
 * 
 * A stream is TLAPM output for a given module.
 * 
 * @author Daniel Ricketts
 * @version $Id$
 */
public class TLAPMBroadcastStreamListener implements IStreamListener
{
    private IProverProcessOutputSink[] listeners = null;

    /**
     * Constructs a stream listener for output for the given modulePath.
     * This is the modulePath that will be sent to all listeners for TLAPM
     * output.
     * 
     * The constructor also takes a progress monitor. This monitor can be sent to listeners
     * to TLC output so that they can report progress.
     * 
     * @param monitor
     * 
     * @param modulePathString.
     * @param description the description of the prover launch. Contains information about
     * the parameters used to launch the prover.
     */
    public TLAPMBroadcastStreamListener(IPath modulePath, ProverLaunchDescription description, IProgressMonitor monitor)
    {
        this.listeners = getRegisteredStreamManagers(modulePath, description, monitor);
    }

    /* (non-Javadoc)
     * @see org.eclipse.debug.core.IStreamListener#streamAppended(java.lang.String, org.eclipse.debug.core.model.IStreamMonitor)
     */
    public synchronized void streamAppended(String text, IStreamMonitor monitor)
    {
        // broadcast the message
        for (int i = 0; i < listeners.length; i++)
        {
            if (listeners[i] != null)
            {
                try
                {
                    listeners[i].appendText(text);
                } catch (Exception e)
                {
                    ProverUIActivator.logError("Error broadcasting the message", e);
                }
            }
        }
    }

    /**
     * Inform the listeners about completion.
     */
    public synchronized void streamClosed()
    {
        // broadcast the message
        for (int i = 0; i < listeners.length; i++)
        {
            try
            {

                if (listeners[i] != null)
                {
                    listeners[i].processFinished();
                }
            } catch (Exception e)
            {
                ProverUIActivator.logError("Error broadcasting the stream closed event", e);
            }
        }
    }

    /**
     * Creates a {@link ConsoleProverProcessOutputSink} and a {@link ParsingProverProcessOutputSink}.
     * 
     * Calls {@link IProverProcessOutputSink#initializeSink(IPath, ProverLaunchDescription, IProgressMonitor)} for each of those sinks
     * with the modulePath, description, and monitor. The monitor can be used to report progress on TLC's output.
     * 
     * @param monitor TODO
     * 
     * @return an array of the instantiated sinks.
     */
    public static IProverProcessOutputSink[] getRegisteredStreamManagers(IPath modulePath,
            ProverLaunchDescription description, IProgressMonitor monitor)
    {
        IProverProcessOutputSink[] outputSinks = new IProverProcessOutputSink[] { new ConsoleProverProcessOutputSink(),
                new ParsingProverProcessOutputSink() };
        outputSinks[0].initializeSink(modulePath, description, monitor);
        outputSinks[1].initializeSink(modulePath, description, monitor);
        return outputSinks;
    }
}
