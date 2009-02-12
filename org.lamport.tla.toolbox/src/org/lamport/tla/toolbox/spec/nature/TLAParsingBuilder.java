package org.lamport.tla.toolbox.spec.nature;

import java.util.List;
import java.util.Map;
import java.util.Vector;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;

/**
 * The parsing builder
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAParsingBuilder extends IncrementalProjectBuilder
{
    public static final String BUILDER_ID = "toolbox.builder.TLAParserBuilder";


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

    protected IProject[] build(int kind, Map args, IProgressMonitor monitor) throws CoreException
    {
        if (getProject() != Activator.getSpecManager().getSpecLoaded().getProject())
        {
            // skip the build calls on wrong projects (which are in WS, but not a current spec)
            return null;
        }
        
        System.out.println("----\n");
        // TODO !!! look how the monitors should be treated !!!
        // and then invoke monitor.begin

        if (IncrementalProjectBuilder.FULL_BUILD == kind)
        {
            // explicit full build
            // on workspace start
            // or after clean
            ParserHelper.rebuildSpec(monitor);
        } else
        {
            // an incremental build
            // triggered manually or by resource modification 
            IResourceDelta delta = getDelta(getProject());
            if (delta == null)
            {
                // no increment found, run a full build
                ParserHelper.rebuildSpec(monitor);
                // runFullBuild(monitor);
            } else
            {
                /*
                 * The delta is a tree, with a root element pointing to the containing project,
                 * and children indicating the files
                 * 
                 * Run a visitor on it in order to find out the changed files
                 */
                ChangedModulesGatheringDeltaVisitor moduleFinder = new ChangedModulesGatheringDeltaVisitor();
                delta.accept(moduleFinder);

                IResource rootFile = null;
                Spec spec = Activator.getSpecManager().getSpecLoaded();
                if (spec != null)
                {
                    rootFile = spec.getRootFile();
                }

                for (int i = 0; i < moduleFinder.modules.size(); i++)
                {
                    String changedModule = (String) moduleFinder.modules.get(i);

                    // call build on the changed resource
                    // if the file is a Root file it will call buildSpec
                    // otherwise buildModule is invoked
                    build(changedModule, rootFile, monitor);
                    
                    List modulesToRebuild = Activator.getModuleDependencyStorage().getListOfModules(changedModule);
                    // iterate over modules and rebuild them
                    for (int j = 0; j < modulesToRebuild.size(); j++)
                    {
                        // call build on dependent resources
                        // if the file is a Root file it will call buildSpec
                        // otherwise buildModule is invoked
                        build((String) modulesToRebuild.get(j), rootFile, monitor);
                    }
                }
            }
        }

        System.out.println("----\n");
        // since every project is one spec and we do not want to touch other specs always return NULL!
        return null;
    }
    
    private void build(String moduleFileName, IResource rootFile, IProgressMonitor monitor)
    {
        // if the changed file is a root file - run the spec build
        if (rootFile != null && (rootFile.getName().equals(moduleFileName)))
        {
            // this will rebuild the spec starting from root, and change the spec status
            // still, we want to continue and keep the dependency information about other files
            ParserHelper.rebuildSpec(monitor);
        } else
        {
            // retrieve a resource
            final IResource moduleFile = ResourceHelper.getLinkedFile(getProject(), moduleFileName, false);
            if (moduleFile == null)
            {
                throw new IllegalStateException("Resource not found during build");
            }
            // run the module build
            ParserHelper.rebuildModule(moduleFile, monitor);
        }
    }

    

    /**
     * Visitor to find out what files changed
     * @author Simon Zambrovski
     * @version $Id$
     */
    public class ChangedModulesGatheringDeltaVisitor implements IResourceDeltaVisitor
    {
        Vector modules = new Vector();

        public ChangedModulesGatheringDeltaVisitor()
        {
        }
        /**
         * @see org.eclipse.core.resources.IResourceDeltaVisitor#visit(org.eclipse.core.resources.IResourceDelta)
         */
        public boolean visit(IResourceDelta delta) throws CoreException
        {
            final IResource resource = delta.getResource();
            if (IResource.FILE == resource.getType())
            {
                // a file found
                if (ResourceHelper.isModule(resource))
                {
                    modules.add(resource.getName());
                }
            }
            // we want the visitor to visit the whole tree
            return true;
        }
    }

}
