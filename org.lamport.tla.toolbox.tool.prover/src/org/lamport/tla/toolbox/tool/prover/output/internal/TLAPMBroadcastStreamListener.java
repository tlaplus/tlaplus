package org.lamport.tla.toolbox.tool.prover.output.internal;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.IStreamListener;
import org.eclipse.debug.core.model.IStreamMonitor;
import org.lamport.tla.toolbox.tool.prover.job.ProverJob;
import org.lamport.tla.toolbox.tool.prover.output.IProverProcessOutputSink;
import org.lamport.tla.toolbox.tool.prover.ui.ConsoleProverProcessOutputSink;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.output.TagBasedTLAPMOutputIncrementalParser;

/**
 * A listener that broadcasts streams to a {@link ConsoleProverProcessOutputSink}
 * and a {@link TagBasedTLAPMOutputIncrementalParser}.
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
     * Constructs a stream listener for output for the given module. This will be passed
     * to listeners of TLAPM output.
     * 
     * The constructor also takes a progress monitor. This monitor can be sent to listeners
     * to TLAPM output so that they can report progress.
     * 
     * The prover job will also be sent to listeners so that they can have access to information
     * and useful data structures pertaining to the launch of the prover.
     * 
     * See {@link #getRegisteredStreamManagers(IFile, ProverJob, IProgressMonitor)} for the creation
     * of listeners.
     * 
     * @param monitor
     * 
     * @param module
     * @param proverJob the job provides access to the description of the prover launch and other
     * useful fields
     */
    public TLAPMBroadcastStreamListener(IFile module, ProverJob proverJob, IProgressMonitor monitor)
    {
        this.listeners = getRegisteredStreamManagers(module, proverJob, monitor);
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
     * When the stream is closed, this method tells all listeners created in
     * {@link #getRegisteredStreamManagers(IFile, ProverJob, IProgressMonitor)} that
     * the stream is closed.
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
     * Creates a {@link ConsoleProverProcessOutputSink} and a {@link TagBasedTLAPMOutputIncrementalParser}.
     * 
     * Calls {@link IProverProcessOutputSink#initializeSink(IFile, ProverJob, IProgressMonitor)} for each of those sinks
     * with the module, job, and monitor. The monitor can be used to report progress on TLAPM's output.
     * 
     * @param monitor TODO
     * 
     * @return an array of the instantiated sinks.
     */
    public static IProverProcessOutputSink[] getRegisteredStreamManagers(IFile module,
            ProverJob proverJob, IProgressMonitor monitor)
    {
        IProverProcessOutputSink[] outputSinks = new IProverProcessOutputSink[] { new ConsoleProverProcessOutputSink(),
                new TagBasedTLAPMOutputIncrementalParser() };
        outputSinks[0].initializeSink(module, proverJob, monitor);
        outputSinks[1].initializeSink(module, proverJob, monitor);
        return outputSinks;
    }
}
