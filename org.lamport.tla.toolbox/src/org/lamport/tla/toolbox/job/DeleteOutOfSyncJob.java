package org.lamport.tla.toolbox.job;

import java.util.List;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.WorkspaceJob;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

/**
 * Delete files out of sync
 * @author Simon Zambrovski
 * @version $Id$
 */
public class DeleteOutOfSyncJob extends WorkspaceJob
{
    private final List<IResource> files;

    /**
     * @param name
     */
    public DeleteOutOfSyncJob(List<IResource> files)
    {
        super("deleteOutOfSyncFiles");
        this.files = files;
    }

    /**
     * @see org.eclipse.core.resources.WorkspaceJob#runInWorkspace(org.eclipse.core.runtime.IProgressMonitor)
     */
    public IStatus runInWorkspace(IProgressMonitor monitor) throws CoreException
    {
        for (int i = 0; i < files.size(); i++)
        {
            files.get(i).delete(true, monitor);
        }
        return Status.OK_STATUS;
    }
}
