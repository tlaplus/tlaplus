package org.lamport.tla.toolbox.tool.tlc.output.internal;

import java.io.ByteArrayInputStream;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class FileProcessOutputSink implements IProcessOutputSink
{
    private ISchedulingRule rule = null;
    private IFile outFile = null;

    public FileProcessOutputSink()
    {

    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#appendText(java.lang.String)
     */
    public void appendText(final String text)
    {
        try
        {
            ResourcesPlugin.getWorkspace().run(new IWorkspaceRunnable() {
                public void run(IProgressMonitor monitor) throws CoreException
                {
                    // System.out.print(Thread.currentThread().getId() + " : " + message);
                    outFile.appendContents(new ByteArrayInputStream(text.getBytes()), IResource.KEEP_HISTORY
                            | IResource.FORCE, monitor);
                }
            }, rule, IResource.NONE, new NullProgressMonitor());

            // if the console output is active, print to it
        } catch (CoreException e)
        {
            e.printStackTrace();
        }

    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#initializeSink(java.lang.String, int)
     */
    public void initializeSink(String processName, int sinkType)
    {

    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink#processFinished()
     */
    public void processFinished()
    {

    }

}
