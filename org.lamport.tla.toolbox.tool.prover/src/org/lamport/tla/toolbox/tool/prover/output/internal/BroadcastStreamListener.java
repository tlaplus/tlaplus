package org.lamport.tla.toolbox.tool.prover.output.internal;

import java.util.Vector;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.Platform;
import org.eclipse.debug.core.IStreamListener;
import org.eclipse.debug.core.model.IStreamMonitor;
import org.lamport.tla.toolbox.tool.prover.ProverActivator;
import org.lamport.tla.toolbox.tool.prover.output.IProverProcessOutputSink;

/**
 * A listener that broadcasts streams to listeners registered to the extension
 * point {@link IProverProcessOutputSink#EXTENSION_ID}.
 * 
 * @author Daniel Ricketts
 * @version $Id$
 */
public class BroadcastStreamListener implements IStreamListener
{
    private IProverProcessOutputSink[] listeners = null;

    /**
     * 
     * @param streamName
     * @param kind, see constants {@link IProcessOutputSink#TYPE_DEBUG}, {@link IProcessOutputSink#TYPE_ERROR}, {@link IProcessOutputSink#TYPE_OUT}
     */
    public BroadcastStreamListener(String streamName, int kind)
    {
        this.listeners = getRegisteredStreamManagers(streamName, kind);
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
                    ProverActivator.logError("Error broadcasting the message", e);
                }
            }
        }
    }

    /**
     * Inform about completion
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
                ProverActivator.logError("Error broadcasting the stream closed event", e);
            }
        }
    }

    /**
     * Retrieves all registered listener managers
     * @return 
     */
    public static IProverProcessOutputSink[] getRegisteredStreamManagers(String name, int type)
    {
        IConfigurationElement[] decls = Platform.getExtensionRegistry().getConfigurationElementsFor(
                IProverProcessOutputSink.EXTENSION_ID);

        Vector validExtensions = new Vector();
        for (int i = 0; i < decls.length; i++)
        {
            try
            {
                IProverProcessOutputSink extension = (IProverProcessOutputSink) decls[i]
                        .createExecutableExtension("class");
                extension.initializeSink(name, type);
                validExtensions.add(extension);
            } catch (CoreException e)
            {
                ProverActivator.logError("Error instatiating the IProcessSink extension", e);
            }
        }
        return (IProverProcessOutputSink[]) validExtensions
                .toArray(new IProverProcessOutputSink[validExtensions.size()]);
    }
}
