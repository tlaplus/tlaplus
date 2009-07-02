package org.lamport.tla.toolbox.tool.tlc.job;

import java.io.ByteArrayInputStream;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * Creates the stub for modelecking, extending the specification root module
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAModelFilesCreationOperation implements IWorkspaceRunnable
{
    // project to create files in
    private IProject project;
    // path to the root module, which name will be added after EXTEND keyword
    // the .tla and .cfg files will be createed in the same directory
    // as the rootModule
    private IPath rootModulePath;

    /**
     * Construct an operation for creation of the files for model checking 
     * @param project project to link files into 
     * @param rootModulePath root module to be extended
     */
    public TLAModelFilesCreationOperation(IProject project, IPath rootModulePath)
    {
        this.rootModulePath = rootModulePath;
        this.project = project;
    }

    /* (non-Javadoc)
     * @see org.eclipse.core.resources.IWorkspaceRunnable#run(org.eclipse.core.runtime.IProgressMonitor)
     */
    public void run(IProgressMonitor monitor) throws CoreException
    {
        monitor.beginTask("Creating files", 2);
        // foo.tla
        String rootModuleFilename = this.rootModulePath.lastSegment();
        // foo
        String rootModuleName = ResourceHelper.getModuleName(rootModuleFilename);
        
        String tlaModuleName = "MC";
        
        IPath tlaPath = this.rootModulePath.removeLastSegments(1).append(tlaModuleName).addFileExtension("tla");
        IPath cfgPath = this.rootModulePath.removeLastSegments(1).append(tlaModuleName).addFileExtension("cfg");

        byte[] content = ResourceHelper.getExtendingModuleContent(tlaModuleName, rootModuleName).append(
                ResourceHelper.getModuleClosingTag()).toString().getBytes();
        
        try
        {

            IFile tlaFile = project.getFile(tlaPath);
            tlaFile.create(new ByteArrayInputStream(content), false /* force*/, new SubProgressMonitor(monitor, 1));
            
            IFile cfgFile = project.getFile(cfgPath);
            cfgFile.create(new ByteArrayInputStream("".getBytes()), false /* force*/, new SubProgressMonitor(monitor, 1));

        } finally {
            monitor.done();
        }
    }

}
