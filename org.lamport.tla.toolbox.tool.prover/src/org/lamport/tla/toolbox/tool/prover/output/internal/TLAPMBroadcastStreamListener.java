package org.lamport.tla.toolbox.tool.prover.output.internal;

import java.util.Vector;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Platform;
import org.eclipse.debug.core.IStreamListener;
import org.eclipse.debug.core.model.IStreamMonitor;
import org.lamport.tla.toolbox.tool.prover.ProverActivator;
import org.lamport.tla.toolbox.tool.prover.output.IProverProcessOutputSink;

/**
 * A listener that broadcasts streams to listeners registered to the extension
 * point {@link IProverProcessOutputSink#EXTENSION_ID}.
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
     * Constructs a stream listener for output for the given processName.
     * This is the name that will be sent to all listeners for TLAPM
     * output. 
     * 
     * In the case of launches of the prover for output for a single module.
     * This name should be the String generate by calling {@link IPath#toPortableString()} on
     * an existing {@link IPath} to the module.
     * 
     * @param modulePathString.
     * @param kind, see constants {@link IProcessOutputSink#TYPE_DEBUG}, {@link IProcessOutputSink#TYPE_ERROR}, {@link IProcessOutputSink#TYPE_OUT}
     */
    public TLAPMBroadcastStreamListener(String processName, int kind)
    {
        this.listeners = getRegisteredStreamManagers(processName, kind);
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
                ProverActivator.logError("Error broadcasting the stream closed event", e);
            }
        }
    }

    /**
     * Retrieves all {@link IProverProcessOutputSink}'s registered at the extension
     * point {@link IProverProcessOutputSink#EXTENSION_ID}.
     * 
     * Calls {@link IProverProcessOutputSink#initializeSink(IPath, int)} for each sink
     * with the processName and type.
     * 
     * @return an array of registered listeners.
     */
    public static IProverProcessOutputSink[] getRegisteredStreamManagers(String processName, int type)
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
                extension.initializeSink(processName, type);
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
