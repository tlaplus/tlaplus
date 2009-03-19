package org.lamport.tla.toolbox.tool.tlc.job;

import java.io.File;
import java.io.IOException;

import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;

/**
 * Create a config file
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ConfigCreationOperation implements IWorkspaceRunnable
{
    private final IPath configPath;
    
    
    /**
     * @param configFilename
     */
    public ConfigCreationOperation(IPath configPath)
    {
        this.configPath = configPath;
        
    }
    
    
    /**
     * @see org.eclipse.core.resources.IWorkspaceRunnable#run(org.eclipse.core.runtime.IProgressMonitor)
     */
    public void run(IProgressMonitor monitor) throws CoreException
    {
        try
        {
            // create file
            File file = new File(configPath.toOSString());
/*          
            if (file.exists())
            {
                return;
            }
*/            
            if (file.createNewFile())
            {
                // successfully created
            } else
            {
                throw new RuntimeException("Error creating a file " + configPath);
            }
        } catch (IOException e)
        {
            throw new CoreException( new Status(Status.ERROR, TLCActivator.PLUGIN_ID, "Error creating CFG file", e));
        }


    }



}
