package org.lamport.tla.toolbox.tool.tlc.launch;

import java.util.List;

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
    
    /**
     * Constructs new model writer
     */
    public ModelWriter()
    {
        this.tlaBuffer = new StringBuffer();
        this.cfgBuffer = new StringBuffer();
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
        cfgBuffer.append("SPECIFICATION ");
        cfgBuffer.append(specDefinition[0]).append(CR);
        tlaBuffer.append(specDefinition[1]).append(CR);
    }
    
    /**
     * Puts (String[])element[0] to CFG file and element[1] to TLA_MC file
     * 
     * @param elements a list of String[] elements
     * @param keyword the keyword to be used in the CFG file
     */
    public void addFormulaList(List elements, String keyword)
    {
        if (elements.isEmpty())
        {
            return;
        }
        cfgBuffer.append("\n\\* " + keyword + " definition\n");
        tlaBuffer.append("\n\\* " + keyword + " definition\n");
        cfgBuffer.append(keyword).append(CR);
        
        for (int i=0; i < elements.size(); i++)
        {
            String[] element = (String[]) elements.get(i);
            cfgBuffer.append(element[0]).append(CR);
            tlaBuffer.append(element[1]).append(CR);
        }
    }


}
