package org.lamport.tla.toolbox.spec.nature;

import java.util.Hashtable;
import java.util.Iterator;
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
import org.eclipse.core.runtime.SubProgressMonitor;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.util.ChangedModulesGatheringDeltaVisitor;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/**
 * The parsing builder
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAParsingBuilder extends IncrementalProjectBuilder
{
    public static final String BUILDER_ID = "toolbox.builder.TLAParserBuilder";

    protected void clean(IProgressMonitor monitor) throws CoreException
    {
        Activator.getDefault().logDebug("Clean has been invoked");
        // clean removes all markers
        Spec spec = Activator.getSpecManager().getSpecLoaded();
        TLAMarkerHelper.removeProblemMarkers(spec.getProject(), monitor);

        /*
         * Forget the state
         */
        forgetLastBuiltState();

    }

    /* (non-Javadoc)
     * @see org.eclipse.core.resources.IncrementalProjectBuilder#build(int, java.util.Map, org.eclipse.core.runtime.IProgressMonitor)
     */
    protected IProject[] build(int kind, @SuppressWarnings("rawtypes") Map args, IProgressMonitor monitor) throws CoreException
    {
        Spec spec = Activator.getSpecManager().getSpecLoaded();
        if (spec == null || getProject() != spec.getProject())
        {
            // skip the build calls on wrong projects (which are in WS, but not
            // a current spec)
            return null;
        }

        /*
         * In July 2013, LL discovered that the "Reparse specification on spec module save" preference 
         * had stopped working.  (Once upon a time it did work, but on examining the code, he saw no 
         * reason why it should ever have worked, so someone must have screwed up the code without leaving
         * a suitable trace.)  See the comments below made on 23 July 2013.
         * On 23 July 2013 LL added the second disjunct to the following `if' test. 
         * A tiny bit of testing reveals that this seems to have fixed the problem, and it seems that the worst
         * thing the change can do is reparse the entire spec when it shouldn't.  But since LL has no idea
         * how things actually work, he has little confidence in this change.
         */
        if (IncrementalProjectBuilder.FULL_BUILD == kind 
        		|| PreferenceStoreHelper.getInstancePreferenceStore().getBoolean(
                        IPreferenceConstants.I_PARSE_SPEC_ON_MODIFY))
        {
            monitor.beginTask("Invoking the SANY to re-parse the spec", IProgressMonitor.UNKNOWN);
            // explicit full build
            // on workspace start
            // or after clean
            ParserHelper.rebuildSpec(new SubProgressMonitor(monitor, IProgressMonitor.UNKNOWN));
            monitor.done();
        } else
        {
            // an incremental build
            // triggered manually or by resource modification
            IResourceDelta delta = getDelta(getProject());
            if (delta == null)
            {
                monitor.beginTask("Invoking the SANY to re-parse the spec", IProgressMonitor.UNKNOWN);
                // no increment found, run a full build
                ParserHelper.rebuildSpec(new SubProgressMonitor(monitor, IProgressMonitor.UNKNOWN));

                monitor.done();
            } else
            {
                /*
                 * The delta is a tree, with a root element pointing to the
                 * containing project, and children indicating the files
                 * 
                 * Run a visitor on it in order to find out the changed files
                 */
                ChangedModulesGatheringDeltaVisitor moduleFinder = new ChangedModulesGatheringDeltaVisitor();
                delta.accept(moduleFinder);

                IResource rootFile = null;
                if (spec != null)
                {
                    rootFile = spec.getRootFile();
                }

                // LL comment added 23 July 2013:  Because of the change made above on this date,
                // control should never get here unless the next statement sets buildSpecOnly
                // to false.  However, the way this value is used, setting it true seems to cause
                // the spec to be rebuilt only when reparsing the root module, which should cause the
                // spec to be rebuilt anyway.  So I have no idea what the writer of this code thought
                // he was doing.
                boolean buildSpecOnly = PreferenceStoreHelper.getInstancePreferenceStore().getBoolean(
                        IPreferenceConstants.I_PARSE_SPEC_ON_MODIFY);

                // this preference is no longer an option
                // 22 Oct 2009
                /*boolean buildFiles = PreferenceStoreHelper
                		.getInstancePreferenceStore().getBoolean(
                				IPreferenceConstants.I_PARSE_FILES_ON_MODIFY);*/

                for (int i = 0; i < moduleFinder.getModules().size(); i++)
                {

                    IResource changedModule = (IResource) moduleFinder.getModules().get(i);

                    // call build on the changed resource
                    // if the file is a Root file it will call buildSpec
                    // otherwise buildModule is invoked
                    build(changedModule.getProjectRelativePath().toString(), rootFile, new SubProgressMonitor(monitor,
                            IProgressMonitor.UNKNOWN));

                    // get the modules to rebuild
                    List<String> modulesToRebuild = Activator.getModuleDependencyStorage().getListOfModulesToReparse(
                            changedModule.getProjectRelativePath().toString());

                    // iterate over modules and rebuild them
                    for (int j = 0; j < modulesToRebuild.size(); j++)
                    {
                        String moduleToBuild = (String) modulesToRebuild.get(j);

                        // root module found
                        if (buildSpecOnly && rootFile != null && rootFile.getName().equals(moduleToBuild))
                        {
                            build(moduleToBuild, rootFile, new SubProgressMonitor(monitor, IProgressMonitor.UNKNOWN));
                            // for this build the root module is already found
                            // do not need to look for it again
                            buildSpecOnly = false;
                            continue;

                        } else
                        {
                            Activator.getDefault().logDebug("There is a root file, but the setting AUTO_BUILD_SPEC is off.");
                        }

                        // this is no longer an option for the user
                        /*if (buildFiles) {
                        	// call build on dependent resources
                        	// if the file is a Root file it will call buildSpec
                        	// otherwise buildModule is invoked
                        	build(moduleToBuild, rootFile,
                        			new SubProgressMonitor(monitor,
                        					IProgressMonitor.UNKNOWN));
                        } else {
                        	Activator
                        			.logDebug("There are dependent files, but the setting AUTO_BUILD_FILES is off.");
                        }*/
                    }
                }
            }
        }

        // since every project is one spec and we do not want to touch other
        // specs always return NULL!
        return null;
    }

    private void build(String moduleFileName, IResource rootFile, IProgressMonitor monitor)
    {
        // if the changed file is a root file - run the spec build
        if (rootFile != null && (rootFile.getName().equals(moduleFileName)))
        {
            monitor.beginTask("Invoking the SANY to re-parse the spec", IProgressMonitor.UNKNOWN);
            // this will rebuild the spec starting from root, and change the
            // spec status
            // still, we want to continue and keep the dependency information
            // about other files
            ParserHelper.rebuildSpec(new SubProgressMonitor(monitor, IProgressMonitor.UNKNOWN));

            monitor.done();
        } else
        {
            // retrieve a resource
            IProject project = getProject();
            // get the file
            IResource moduleFile = project.getFile(moduleFileName);

            /*
             * At this point of time, all modules should have been linked if
             * (!moduleFile.exists()) { moduleFile =
             * ResourceHelper.getLinkedFile(project, moduleFileName, false); }
             */

            if (moduleFile == null || !moduleFile.exists())
            {
                throw new IllegalStateException("Resource not found during build: " + moduleFileName);
            }

            // never build derived resources
            if (!moduleFile.isDerived())
            {
                monitor.beginTask("Invoking SANY to re-parse a module " + moduleFileName, IProgressMonitor.UNKNOWN);
                // run the module build
                ParserHelper.rebuildModule(moduleFile, new SubProgressMonitor(monitor, IProgressMonitor.UNKNOWN));

                monitor.done();
            } else
            {
                Activator.getDefault().logDebug("Skipping resource: " + moduleFileName);
            }
        }

    }

    public static class OutOfBuildSpecModulesGatheringDeltaVisitor implements IResourceDeltaVisitor
    {
        Vector<IResource> modules = new Vector<IResource>();
        Hashtable<String, String> dependancyTable = null;
        Spec spec = null;

        public OutOfBuildSpecModulesGatheringDeltaVisitor()
        {
            // We cannot get the spec manager if it has not been instantiated
            // because this would trigger a resource change event, and this code
            // is being called within a resourceChanged method. Such an
            // infinite loop is not allowed.
            if (Activator.isSpecManagerInstantiated())
            {
                spec = Activator.getSpecManager().getSpecLoaded();
                if (spec != null)
                {
                    String specRootFileName = spec.getRootFile().getName();
                    List<String> dependancyList = Activator.getModuleDependencyStorage().getListOfExtendedModules(
                            specRootFileName);
                    dependancyTable = new Hashtable<String, String>(dependancyList.size());
                    dependancyTable.put(specRootFileName, specRootFileName);
                    Iterator<String> iterator = dependancyList.iterator();
                    while (iterator.hasNext())
                    {
                        String moduleName = iterator.next();
                        dependancyTable.put(moduleName, moduleName);
                    }
                }
            }
        }

        /**
         * @see org.eclipse.core.resources.IResourceDeltaVisitor#visit(org.eclipse.core.resources.IResourceDelta)
         */
        public boolean visit(IResourceDelta delta) throws CoreException
        {
            IResource resource = delta.getResource();
            if (resource.exists() && IResource.FILE == resource.getType())
            {
                // a file found
                if (ResourceHelper.isModule(resource))
                {
                    // if the spec is null, this means that we are unable to get
                    // access to the spec manager
                    // because it has not yet been instantiatec. Instantiating
                    // it would trigger a resource change
                    // event which is not allowed
                    if (spec == null)
                    {
                        modules.add(resource);

                    } else if (spec.getRootFile().getParent().equals(resource.getParent()))
                    {
                        // we are only concerned with modules in the same
                        // directory as the root module because those are the
                        // only ones allowed to be a part of the spec
                        if (resource.getPersistentProperty(TLAParsingBuilderConstants.LAST_BUILT) == null)
                        {
                            if (spec.getStatus() < IParseConstants.PARSED && spec.getStatus() > IParseConstants.UNKNOWN)
                            {
                                // If the property has never been set, the
                                // resource has never been built. If the
                                // current status is parsed, then it cannot be
                                // relevant because it would have been built
                                // if it were relevant. If the status is
                                // unknown, it should remain unknown. In all
                                // other cases, it is possible that the resource
                                // is relevant but it is not known because there
                                // was not a successful parse. Conservatively we
                                // should consider it relevant.
                                modules.add(resource);
                            }
                        }
                        // If there current spec status is a problem status (see
                        // AdaptorFactory.isProblemStatus),
                        // then it is not known whether a given resource is
                        // relevant so all resources are considered
                        // relevant. Relevant resources are not necessarily in
                        // dependancy storage. Any resource that is
                        // out of build when the parse status is error is added to
                        // the list of modules.
                        else if (Long.parseLong(resource.getPersistentProperty(TLAParsingBuilderConstants.LAST_BUILT)) < resource
                                .getLocalTimeStamp()
                                && (dependancyTable.containsKey(resource.getName()) || (spec.getStatus() < IParseConstants.PARSED && spec
                                        .getStatus() > IParseConstants.UNPARSED)))
                        {
                            modules.add(resource);
                        }
                    }
                }
            }
            // we want the visitor to visit the whole tree
            return true;
        }

        /**
         * Retrieves found modules, or an empty list, if nothing found
         * 
         * @return a list with found modules
         */
        public List<IResource> getModules()
        {
            return modules;
        }
    }

}
