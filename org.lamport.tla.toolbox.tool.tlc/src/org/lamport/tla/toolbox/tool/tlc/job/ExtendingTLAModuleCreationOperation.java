package org.lamport.tla.toolbox.tool.tlc.job;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;

import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * Creates the stub for modelecking, extending the specification root module
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ExtendingTLAModuleCreationOperation implements IWorkspaceRunnable
{

    private String modelName;
    private IPath modelRootPath;

    /**
     * @param modelName 
     * @param modelRootPath 
     * @param name
     */
    public ExtendingTLAModuleCreationOperation(IPath modelRootPath, String modelName)
    {
        this.modelRootPath = modelRootPath;
        this.modelName = modelName;
    }

    /* (non-Javadoc)
     * @see org.eclipse.core.resources.IWorkspaceRunnable#run(org.eclipse.core.runtime.IProgressMonitor)
     */
    public void run(IProgressMonitor monitor) throws CoreException
    {
        String moduleFileName = modelRootPath.lastSegment();

        byte[] content = ResourceHelper.getExtendingModuleContent(moduleFileName, modelName).append(ResourceHelper.getModuleClosingTag()).toString().getBytes();
        try
        {
            // create file
            File file = new File(modelRootPath.toOSString());
            if (file.createNewFile())
            {
                // successfully created
                // TODO file editor input
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
            throw new CoreException( new Status(Status.ERROR, TLCActivator.PLUGIN_ID, "Error creating TLA+ file", e));
        }
    }

}
