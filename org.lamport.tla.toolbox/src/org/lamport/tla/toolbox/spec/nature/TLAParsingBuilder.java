package org.lamport.tla.toolbox.spec.nature;

import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.ModuleParserLauncher;
import org.lamport.tla.toolbox.spec.parser.SpecificationParserLauncher;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;

/**
 * The parsing builder
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAParsingBuilder extends IncrementalProjectBuilder
{
    public static final String BUILDER_ID = "toolbox.builder.TLAParserBuilder";

    private final ModuleParserLauncher moduleParser = new ModuleParserLauncher();
    private final SpecificationParserLauncher launcher = new SpecificationParserLauncher(moduleParser);

    protected void clean(IProgressMonitor monitor) throws CoreException
    {
        System.out.println("Clean has been invoked");

        Spec spec = Activator.getSpecManager().getSpecLoaded();
        TLAMarkerHelper.removeProblemMarkers(spec.getProject(), monitor);

        /*
         * Forget the state
         */
        forgetLastBuiltState();

    }

    /**
     * @see org.eclipse.core.resources.IncrementalProjectBuilder#build(int, java.util.Map, org.eclipse.core.runtime.IProgressMonitor)
     */
    protected IProject[] build(int kind, Map args, IProgressMonitor monitor) throws CoreException
    {

        /*
        if (ResourcesPlugin.getWorkspace().isAutoBuilding())
        {
            System.out.println("Running a Build (auto-builing is on): " + kind);
        } else
        {
            System.out.println("Running a Build (auto-builing is off): " + kind);
        }
        */

        if (IncrementalProjectBuilder.FULL_BUILD == kind)
        {
            /* 
             * a full build
             */
            /*
            System.out.println("Full build started");
            */
            runFullBuild(monitor);

        } else
        {

            /*
            if (IncrementalProjectBuilder.AUTO_BUILD == kind)
            {
                System.out.println("Auto build started");
            } else if (IncrementalProjectBuilder.INCREMENTAL_BUILD == kind)
            {
                System.out.println("Incremental build started");
            }
            */

            /*
             *  incremental build
             */
            IResourceDelta delta = getDelta(getProject());
            if (delta == null)
            {
                runFullBuild(monitor);
            } else
            {

                IResource rootFile = null;
                Spec spec = Activator.getSpecManager().getSpecLoaded();
                if (spec != null)
                {
                    rootFile = spec.getRootFile();
                }
                // if the changed file is a root file - run full build
                if (rootFile != null && (rootFile.equals(delta.getResource())))
                    //|| rootFile.getProject().equals(delta.getResource().getProject())
                {
                    runFullBuild(monitor);
                } else {
                    // run incremental build
                    runIncrementalBuild(delta, monitor);
                }
            }
        }

        // since no deltas should be recalculated, return null.
        // this could change in the future
        return null;
    }

    /**
     * Runs a the project builder 
     * @param monitor
     */
    private void runFullBuild(IProgressMonitor monitor)
    {
        // TODO handle the monitor
        try
        {
            getProject().accept(new SpecificationRootFileParsingVisitor());
        } catch (CoreException e)
        {
            // TODO
            e.printStackTrace();
        }
    }

    /**
     * Runs incremental builder
     * @param delta - a resource delta
     * @param monitor 
     */
    private void runIncrementalBuild(IResourceDelta delta, IProgressMonitor monitor)
    {
        // TODO handle the monitor
        try
        {
            delta.accept(new ModuleParsingVisitor());
        } catch (CoreException e)
        {
            // TODO
            e.printStackTrace();
        }
    }

    /**
     * Incremental builder that parses specified TLA+ module
     * @author Simon Zambrovski
     * @version $Id$
     */
    public class ModuleParsingVisitor implements IResourceDeltaVisitor
    {
        IProgressMonitor monitor = null; // TODO init the monitor

        /**
         * @see org.eclipse.core.resources.IResourceDeltaVisitor#visit(org.eclipse.core.resources.IResourceDelta)
         */
        public boolean visit(IResourceDelta delta) throws CoreException
        {
            final IResource resource = delta.getResource();
            System.out.println("Incremental build invoked on " + resource.getName() + " ...");
            IWorkspaceRunnable run = new IWorkspaceRunnable() {

                public void run(IProgressMonitor monitor) throws CoreException
                {

                    TLAMarkerHelper.removeProblemMarkers(resource, monitor);
                    int status = moduleParser.parseModule(resource, monitor);
                    // System.out.println("Resulting status is: " + AdapterFactory.getStatusAsString(spec));
                }
            };
            delta.getResource().getWorkspace().run(run, monitor);
            System.out.println("... build invocation finished.");
            return true;
        }

    }

    /**
     * Visits the project and parses the associated specification root module
     * @author Simon Zambrovski
     * @version $Id$
     */
    public class SpecificationRootFileParsingVisitor implements IResourceVisitor
    {
        IProgressMonitor monitor = null;

        /**
         * @see org.eclipse.core.resources.IResourceVisitor#visit(org.eclipse.core.resources.IResource)
         */
        public boolean visit(IResource resource) throws CoreException
        {
            if (resource instanceof IProject && ((IProject) resource).hasNature(TLANature.ID))
            {
                System.out.println("Full build invoked on " + resource.getName() + " ...");
                // TODO improve this...
                // better: lookup in the project property for the spec name
                // and search a spec by name

                final Spec spec = Activator.getSpecManager().getSpecLoaded();
                if (spec != null && spec.getProject().equals(((IProject) resource)))
                {
                    IWorkspaceRunnable run = new IWorkspaceRunnable() {

                        public void run(IProgressMonitor monitor) throws CoreException
                        {

                            TLAMarkerHelper.removeProblemMarkers(spec.getProject(), monitor);
                            launcher.parseSpecification(spec, monitor);
                            System.out.println("Resulting status is: " + AdapterFactory.getStatusAsString(spec));
                        }
                    };
                    resource.getWorkspace().run(run, monitor);
                    System.out.println("... build invocation finished.");
                } else {
                    System.out.println("... build skipped.");
                }
            }

            // invoke only on the IProject, never on the single module files
            return false;
        }
    }

}
