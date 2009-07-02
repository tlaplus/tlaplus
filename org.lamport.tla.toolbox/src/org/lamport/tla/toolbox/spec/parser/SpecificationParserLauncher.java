package org.lamport.tla.toolbox.spec.parser;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;

/**
 * A specification parser parses the root file of the specification
 * @author Simon Zambrovski
 * @version $Id$
 */
public class SpecificationParserLauncher
{
    private ModuleParserLauncher moduleParser = null;

    public SpecificationParserLauncher(ModuleParserLauncher moduleParser)
    {
         this.moduleParser = moduleParser;
    }
    
    /**
     * Launches the spec parsing
     * @param spec specification handle
     * @param monitor the monitor to report progress
     * @return the parse status (which is also saved in the spec)
     */
    public int parseSpecification(Spec spec, IProgressMonitor monitor)
    {
        // parsed resource is the root file
        IResource parseResource = spec.getRootFile();

        // reset problems from previous run
        TLAMarkerHelper.removeProblemMarkers(parseResource.getProject(), monitor, TLAMarkerHelper.TOOLBOX_MARKERS_TLAPARSER_MARKER_ID);
        
        // call module parse on the root file
        ParseResult result = moduleParser.parseModule(parseResource, monitor);

        // set the status back into the spec
        spec.setStatus(result.getStatus());
        
        if (!AdapterFactory.isProblemStatus(result.getStatus())) 
        {
            spec.setSpecObj(result.getSpecObj());
        }
        
        return result.getStatus();
    }

}
