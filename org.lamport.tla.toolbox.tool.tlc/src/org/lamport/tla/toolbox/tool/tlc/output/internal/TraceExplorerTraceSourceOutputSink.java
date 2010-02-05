package org.lamport.tla.toolbox.tool.tlc.output.internal;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * Clears MC_TE.out and then writes TLC output to it.
 * 
 * @author Daniel Ricketts
 *
 */
public class TraceExplorerTraceSourceOutputSink extends FileProcessOutputSink
{

    private boolean isTraceExplorerOutput;
    private boolean clearFile;

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#appendText(java.lang.String)
     */
    public synchronized void appendText(final String text)
    {
        // we dont want to do anything if this is a run of the trace explorer
        if (isTraceExplorerOutput)
        {
            return;
        }
        if (clearFile)
        {
            // // try
            // // {
            // // ResourcesPlugin.getWorkspace().run(new IWorkspaceRunnable() {
            // // public void run(IProgressMonitor monitor) throws CoreException
            // // {
            // // // System.out.print(Thread.currentThread().getId() + " : " + message);
            // // outFile.setContents(new ByteArrayInputStream("".getBytes()), IResource.KEEP_HISTORY
            // // | IResource.FORCE | IResource.DERIVED, monitor);
            // // }
            // // }, rule, IWorkspace.AVOID_UPDATE, new NullProgressMonitor());
            // //
            // // // if the console output is active, print to it
            // // } catch (CoreException e)
            // // {
            // // TLCActivator.logError("Error clearing the trace explorer trace source file for " + processName, e);
            // // }
            ModelHelper.createOrClearFiles(new IFile[] { this.outFile }, new NullProgressMonitor());
            clearFile = false;
        }
        super.appendText(text);
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#initializeSink(java.lang.String, int)
     */
    public void initializeSink(String processName, int sinkType)
    {
        this.isTraceExplorerOutput = sinkType == IProcessOutputSink.TYPE_TRACE_EXPLORE;
        this.processName = processName;
        ILaunchConfiguration config = ModelHelper.getModelByName(processName);

        this.outFile = ModelHelper.getTraceSourceFile(config);
        this.rule = ResourceHelper.getModifyRule(outFile);

        // flag the output file to be cleared before the first text is appended
        this.clearFile = true;
    }

}
