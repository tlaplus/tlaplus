package org.lamport.tla.toolbox.tool.tlc.output.internal;

import java.io.ByteArrayInputStream;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * Sink writing the MC.out file
 * @author Simon Zambrovski
 */
public class FileProcessOutputSink implements IProcessOutputSink
{
    protected ISchedulingRule rule;
    protected IFile outFile;
	private Model model;

    public FileProcessOutputSink()
    {

    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#appendText(java.lang.String)
     */
    public synchronized void appendText(final String text)
    {
        try
        {
            ResourcesPlugin.getWorkspace().run(new IWorkspaceRunnable() {
                public void run(IProgressMonitor monitor) throws CoreException
                {
                    // System.out.print(Thread.currentThread().getId() + " : " + message);
                    outFile.appendContents(new ByteArrayInputStream(text.getBytes()), IResource.FORCE, monitor);
                }
            }, rule, IWorkspace.AVOID_UPDATE, new NullProgressMonitor());

            // if the console output is active, print to it
        } catch (CoreException e)
        {
            TLCActivator.logError("Error writing the TLC process output file for " + model.getName(), e);
        }

    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#initializeSink(java.lang.String, int)
     */
    public void initializeSink(Model model, int sinkType)
    {
        boolean isTraceExplore = sinkType == TYPE_TRACE_EXPLORE;

        this.model = model;
        this.outFile = model.getOutputLogFile(isTraceExplore);
        this.rule = ResourceHelper.getModifyRule(outFile);
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#processFinished()
     */
    public void processFinished()
    {
        /*
                try
                {
                    ResourcesPlugin.getWorkspace().run(new IWorkspaceRunnable() {

                        public void run(IProgressMonitor monitor) throws CoreException
                        {
                            ResourcesPlugin.getWorkspace().getRoot().refreshLocal(IResource.DEPTH_INFINITE,
                                    new NullProgressMonitor());

                        }
                    }, ResourcesPlugin.getWorkspace().getRoot(), IResource.NONE, new NullProgressMonitor());
                } catch (CoreException e)
                {
                    TLCActivator.getDefault().logError("Error synchronizing the workspace", e);
                }
        */
    }
}
