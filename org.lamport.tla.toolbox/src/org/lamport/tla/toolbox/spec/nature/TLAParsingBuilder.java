package org.lamport.tla.toolbox.spec.nature;

import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.IParserLauncher;
import org.lamport.tla.toolbox.spec.parser.StreamInterpretingParserLauncher;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/**
 * The parsing builder
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAParsingBuilder extends IncrementalProjectBuilder
{
    public static final String BUILDER_ID = "toolbox.builder.TLAParserBuilder";

    private final IParserLauncher launcher = new StreamInterpretingParserLauncher();

    protected void clean(IProgressMonitor monitor) throws CoreException
    {
        System.out.println("Clean has been invoked");
        Spec spec = Activator.getSpecManager().getSpecLoaded();
        // TLAMarkerHelper.deleteMarkers(spec, monitor);
    }

    /**
     * @see org.eclipse.core.resources.IncrementalProjectBuilder#build(int, java.util.Map, org.eclipse.core.runtime.IProgressMonitor)
     */
    protected IProject[] build(int kind, Map args, IProgressMonitor monitor) throws CoreException
    {

        if (PreferenceStoreHelper.getInstancePreferenceStore().getBoolean(
                IPreferenceConstants.P_PARSER_RUN_ON_MODIFICATION))
        {
            System.out.println("Running a Build (on): " + kind);
        } else
        {
            System.out.println("Running a Build (off): " + kind);
        }

        runBuild(monitor);

        forgetLastBuiltState();

        // since no deltas should be recalculated, return null.
        // this could change in the future
        return null;
    }

    /**
     * @param monitor
     */
    private void runBuild(IProgressMonitor monitor)
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
                System.out.println("Build Invoked");
                // TODO improve this...
                // better: lookup in the project property for the spec name
                // and search a spec by name

                final Spec spec = Activator.getSpecManager().getSpecLoaded();
                IWorkspaceRunnable run = new IWorkspaceRunnable(){

                    public void run(IProgressMonitor monitor) throws CoreException
                    {
                        TLAMarkerHelper.deleteMarkers(spec, monitor);
                        launcher.parseSpecification(spec);
                        TLAMarkerHelper.setupProblemInformation(spec, monitor);
                        System.out.println("Resulting status is: " + AdapterFactory.getStatusAsString(spec));
                    }
                };
                resource.getWorkspace().run(run, monitor);

            }

            // invoke only on the IProject, never on the single module files
            return false;
        }
    }

}
