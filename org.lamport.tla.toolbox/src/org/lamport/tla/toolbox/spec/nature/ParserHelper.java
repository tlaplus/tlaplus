package org.lamport.tla.toolbox.spec.nature;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.ModuleParserLauncher;
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
        System.out.println("Module build invoked on " + resource.getName() + " ...");
        IWorkspaceRunnable run = new IWorkspaceRunnable() {

            public void run(IProgressMonitor monitor) throws CoreException
            {

                // markers already removed in the parseModule
                // TLAMarkerHelper.removeProblemMarkers(resource, monitor);
                int status = moduleParser.parseModule(resource, monitor);
                System.out.println("Resulting status is: " + AdapterFactory.getStatusAsString(status));
            }
        };
        try
        {
            resource.getWorkspace().run(run, monitor);
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        System.out.println("... build invocation finished.");
    }

    /**
     * This will run the parse of the root file of the current spec 
     * @param monitor
     */
    public static void rebuildSpec(IProgressMonitor monitor)
    {
        // TODO improve this...
        // better: lookup in the project property for the spec name
        // and search a spec by name

        final Spec spec = Activator.getSpecManager().getSpecLoaded();
        if (spec == null)
        {
            return;
        }
        System.out.println("Spec build invoked on " + spec.getName() + " ...");
        IWorkspaceRunnable run = new IWorkspaceRunnable() {

            public void run(IProgressMonitor monitor) throws CoreException
            {

                // markers already removed in the parseSpecification 
                // TLAMarkerHelper.removeProblemMarkers(spec.getProject(), monitor);
                launcher.parseSpecification(spec, monitor);
                System.out.println("Resulting status is: " + AdapterFactory.getStatusAsString(spec));
            }
        };
        try
        {
            ResourcesPlugin.getWorkspace().run(run, monitor);
        } catch (CoreException e)
        {
            e.printStackTrace();
        }
        System.out.println("... build invocation finished.");
    }
}
