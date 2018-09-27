package org.lamport.tla.toolbox.spec.nature;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.ModuleParserLauncher;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.spec.parser.SpecificationParserLauncher;
import org.lamport.tla.toolbox.util.AdapterFactory;

/**
 * Encapsulates parser launching methods
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParserHelper
{

    private final static ModuleParserLauncher moduleParser = new ModuleParserLauncher();
    private final static SpecificationParserLauncher launcher = new SpecificationParserLauncher(moduleParser);

    /**
     * Runs the parser on the given module
     * @param resource
     * @param monitor
     */
    public static void rebuildModule(final IResource resource, IProgressMonitor monitor)
    {
        if (resource == null)
        {
            return;
        }
        IWorkspaceRunnable run = new IWorkspaceRunnable() {

            public void run(IProgressMonitor monitor) throws CoreException
            {
                moduleParser.parseModule(resource, monitor);
            }
        };
        try
        {
            resource.getWorkspace().run(run, monitor);
        } catch (CoreException e)
        {
            Activator.getDefault().logError("Error parsing a module", e);
        }
    }

    /**
     * This will run the parse of the root file of the current spec 
     * @param monitor
     */
    public static void rebuildSpec(IProgressMonitor monitor)
    {
        final Spec spec = Activator.getSpecManager().getSpecLoaded();
        if (spec == null)
        {
            return;
        }
        IWorkspaceRunnable run = new IWorkspaceRunnable() {

            public void run(IProgressMonitor monitor) throws CoreException
            {
                // markers already removed in the parseSpecification 
                launcher.parseSpecification(spec, monitor);
            }
        };
        try
        {
            ResourcesPlugin.getWorkspace().run(run, monitor);
        } catch (CoreException e)
        {
            Activator.getDefault().logError("Error parsing a module", e);
        }
    }
}
