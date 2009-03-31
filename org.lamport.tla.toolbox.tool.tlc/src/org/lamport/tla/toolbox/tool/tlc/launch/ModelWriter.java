package org.lamport.tla.toolbox.tool.tlc.launch;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * Encapsulates two buffers and provides semantic methods to add content to the _MC file and the CFG file of the model 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelWriter
{
    private static final String CR = "\n";
    
    private StringBuffer tlaBuffer;
    private StringBuffer cfgBuffer;
    
    
    public ModelWriter()
    {
        this.tlaBuffer = new StringBuffer();
        this.cfgBuffer = new StringBuffer();
    }
    
    /**
     * Add file header
     * @param moduleFilename
     * @param extendedModuleName
     */
    public void addPrimer(String moduleFilename, String extendedModuleName)
    {
        tlaBuffer.append(ResourceHelper.getExtendingModuleContent(moduleFilename, extendedModuleName));
    }
    /**
     * Add spec definition
     * @param specDefinition
     */
    public void addSpecDefinition(String[] specDefinition) 
    {
        tlaBuffer.append(specDefinition[1]).append(CR);
        cfgBuffer.append("SPECIFICATION ").append(specDefinition[0]).append(CR);
    }
    
    
    /**
     * Write the content to files
     * @param tlaFile
     * @param cfgFile
     * @param monitor
     * @throws CoreException
     */
    public void writeFiles(IFile tlaFile, IFile cfgFile, IProgressMonitor monitor) throws CoreException
    {
        tlaBuffer.append(ResourceHelper.getModuleClosingTag());    
        ResourceHelper.replaceContent(tlaFile, tlaBuffer, monitor);
        ResourceHelper.replaceContent(cfgFile, cfgBuffer, monitor);
    }
}
