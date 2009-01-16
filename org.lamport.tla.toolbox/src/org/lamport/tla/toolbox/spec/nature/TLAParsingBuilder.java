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

    private IParserLauncher launcher = new StreamInterpretingParserLauncher();
    
    
    
    
    protected void clean(IProgressMonitor monitor) throws CoreException
    {
        super.clean(monitor);
    }

    /**
     * @see org.eclipse.core.resources.IncrementalProjectBuilder#build(int, java.util.Map, org.eclipse.core.runtime.IProgressMonitor)
     */
    protected IProject[] build(int kind, Map args, IProgressMonitor monitor) throws CoreException
    {
        /*
        System.out.println("Build has been invoked");
        */
        switch (kind)
        {
        case INCREMENTAL_BUILD:
            System.out.println("Incremental build");
            break;
        case FULL_BUILD:
            System.out.println("Full build (e.G. on load)");
            break;
        case CLEAN_BUILD:
            System.out.println("Clean build (explicit invocation)");
            break;
        case AUTO_BUILD:
            System.out.println("Auto build (e.G. on saved modification)");
            break;
        default:
            System.out.println("BUG. Unknown build type :" + kind + ".");
        }

        if (PreferenceStoreHelper.getInstancePreferenceStore().getBoolean(
                IPreferenceConstants.P_PARSER_RUN_ON_MODIFICATION))
        {
            if (AUTO_BUILD == kind || FULL_BUILD == kind)
            {
                System.out.println("Running a " + ((kind == AUTO_BUILD) ? "Auto-Build" : "Full-Build"));
                runBuild(monitor);
            }
        } else
        {
            if (CLEAN_BUILD == kind)
            {
                System.out.println("Running a Clean-Build");
                runBuild(monitor);
            }
        }

        // since no deltas should be recalculated, return null.
        // this could change in the future
        return null;
    }

    /**
     * @param monitor
     */
    private void runBuild(IProgressMonitor monitor)
    {
        //TODO handle the monitor
        
        
        final Spec spec = Activator.getSpecManager().getSpecLoaded();
        try
        {
            TLAMarkerHelper.deleteMarkers(spec, monitor);
            getProject().accept(new SpecificationRootFileParsingVisitor());
            TLAMarkerHelper.setupProblemInformation(spec, monitor);
            
            IWorkspaceRunnable runnable = new IWorkspaceRunnable() {

                public void run(IProgressMonitor monitor) throws CoreException
                {

                    Activator.getParserRegistry().parseResultChanged(spec.getStatus());
                }
            };
            getProject().getWorkspace().run(runnable, monitor);
            

        } catch (CoreException e)
        {
            // TODO
            
        }
    }

    /**
     * Visits the project and parses the associated specification root module
     * @author Simon Zambrovski
     * @version $Id$
     */
    public class SpecificationRootFileParsingVisitor implements IResourceVisitor
    {
        /**
         * @see org.eclipse.core.resources.IResourceVisitor#visit(org.eclipse.core.resources.IResource)
         */
        public boolean visit(IResource resource) throws CoreException
        {
            if (resource instanceof IProject && ((IProject) resource).hasNature(TLANature.ID))
            {
                // TODO improve this...
                // better: lookup in the project property for the spec name
                // and search a spec by name
                Spec spec = Activator.getSpecManager().getSpecLoaded();
                
                launcher.parseSpecification(spec);
            }

            // invoke only on the IProject, never on the single module files
            return false;
        }
    }

}
