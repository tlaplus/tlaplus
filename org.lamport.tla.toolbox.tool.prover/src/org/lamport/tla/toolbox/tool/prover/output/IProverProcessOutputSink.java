package org.lamport.tla.toolbox.tool.prover.output;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.lamport.tla.toolbox.tool.prover.output.internal.ProverLaunchDescription;

/**
 * An interface for sinks which receive output from the TLAPM.
 * The sinks receive output through the method {@link #appendText(String)}.
 * They are given a chance to initialize prior to any text being sent
 * through the method {@link #initializeSink(IFile, ProverLaunchDescription, IProgressMonitor)}.
 * The method {@link #processFinished()} indicates that no more text will be
 * sent.
 * 
 * @author Daniel Ricketts
 *
 */
public interface IProverProcessOutputSink
{
    /**
     * Indicates that the sink is receiving output from a launch
     * of the prover in which proving but not checking is done.
     */
    public final static int TYPE_PROVE = 1;
    /**
     * Indicates that the sink is receiving output from a launch
     * of the prover in which checking is done.
     */
    public final static int TYPE_CHECK = 2;

    /**
     * Appends text to the sink.
     * 
     * @param text 
     */
    public void appendText(String text);

    /**
     * Called prior to appending text. Allows the sink to perform any
     * necessary initialization before receiving output from the prover.
     * 
     * The {@link IFile} is a handle on the module on which the prover was launched
     * 
     * @param moduleFile the file handle on the module
     * @param description the description of the prover launch. Contains information about
     * the parameters used to launch the prover.
     * @param monitor a progress monitor that can be used to report progress
     */
    public void initializeSink(IFile moduleFile, ProverLaunchDescription description, IProgressMonitor monitor);

    /**
     * Signal to the sink that the prover process has terminated and no data will be sent.
     */
    public void processFinished();

}
