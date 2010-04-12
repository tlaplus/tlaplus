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
import org.eclipse.debug.core.ILaunchConfiguration;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * Sink writing the MC.out file
 * @author Simon Zambrovski
 * @version $Id$
 */
public class FileProcessOutputSink implements IProcessOutputSink
{
    protected ISchedulingRule rule;
    protected IFile outFile;
    protected String processName;

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
            TLCActivator.logError("Error writing the TLC process output file for " + processName, e);
        }

    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#initializeSink(java.lang.String, int)
     */
    public void initializeSink(String processName, int sinkType)
    {
        boolean isTraceExplore = sinkType == TYPE_TRACE_EXPLORE;

        this.processName = processName;
        ILaunchConfiguration config = ModelHelper.getModelByName(processName);
        this.outFile = ModelHelper.getModelOutputLogFile(config, isTraceExplore);
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
                    TLCActivator.logError("Error synchronizing the workspace", e);
                }
        */
    }
}
