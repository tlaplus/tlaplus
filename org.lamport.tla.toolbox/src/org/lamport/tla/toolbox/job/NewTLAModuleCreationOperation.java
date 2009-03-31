package org.lamport.tla.toolbox.job;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;

import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.WorkspaceJob;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * Creates a new TLA+ module
 * @author Simon Zambrovski
 * @version $Id$
 */
public class NewTLAModuleCreationOperation implements IWorkspaceRunnable
{
    private IPath modulePath;

    /**
     * @param name
     */
    public NewTLAModuleCreationOperation(IPath module)
    {
        this.modulePath = module;
    }

    /* (non-Javadoc)
     * @see org.eclipse.core.resources.IWorkspaceRunnable#run(org.eclipse.core.runtime.IProgressMonitor)
     */
    public void run(IProgressMonitor monitor) throws CoreException
    {
        String moduleFileName = modulePath.lastSegment();

        byte[] content = ResourceHelper.getEmptyModuleContent(moduleFileName).append(ResourceHelper.getModuleClosingTag()).toString().getBytes();
        
        try
        {
            // create file
            File file = new File(modulePath.toOSString());
            if (file.createNewFile())
            {
                // successfully created
                // TODO 
                FileOutputStream fos = new FileOutputStream(file);
                fos.write(content);
                fos.flush();
                fos.close();
            } else
            {
                throw new RuntimeException("Error creating a file");
            }
        } catch (IOException e)
        {
            throw new CoreException( new Status(Status.ERROR, Activator.PLUGIN_ID, "Error creating TLA+ file", e));
        }
        
    }

    /**
     * Job factory
     * @param module
     * @return
     */
    public static WorkspaceJob NEW_JOB(final IPath module)
    {
        return new WorkspaceJob("Creating TLA+ file")
        {
            NewTLAModuleCreationOperation op = new NewTLAModuleCreationOperation(module);

            public IStatus runInWorkspace(IProgressMonitor monitor) throws CoreException
            {
                op.run(monitor);
                return Status.OK_STATUS;
            }
        };
        
    }
}
