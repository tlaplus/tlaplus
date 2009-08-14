package org.lamport.tla.toolbox.tool.tlc.job;

import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.action.Action;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * Abstract TLC job
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class TLCJob extends AbstractJob implements IModelConfigurationConstants, IModelConfigurationDefaults
{

    public static class AllJobMatcher
    {
    }

    protected static final int STEP = 30;
    protected static final long TIMEOUT = 1000 * 1;
    protected IFile rootModule;
    protected IFile cfgFile;
    protected IFile outFile;
    protected IFolder launchDir;
    protected int workers = 1;
    protected ILaunch launch;
    protected String modelName;
    private final String specName;

    protected boolean appendConsole = true;

    /**
     * Creates a TLC job for a given spec and model
     * @param rootModule
     * @param cfgFile
     * @param launchDir
     */
    public TLCJob(String specName, String modelName, ILaunch launch)
    {
        super("TLC run for " + modelName);
        this.specName = specName;
        this.modelName = modelName;

        IProject project = ResourceHelper.getProject(specName);
        Assert.isNotNull(project, "Error accessing the spec project " + specName);

        this.launchDir = project.getFolder(modelName);
        Assert.isNotNull(this.launchDir, "Error accessing the model folder " + modelName);

        this.launch = launch;
        
        this.rootModule = this.launchDir.getFile(ModelHelper.FILE_TLA);
        this.cfgFile = this.launchDir.getFile(ModelHelper.FILE_CFG);
        this.outFile = this.launchDir.getFile(ModelHelper.FILE_OUT);
    }

    /**
     * Reads the model parameters and constructs the corresponding command line arguments
     * @return string array with arguments
     * @throws CoreException
     */
    public String[] constructProgramArguments() throws CoreException
    {
        Vector arguments = new Vector();
        ILaunchConfiguration config = launch.getLaunchConfiguration();

        // deadlock
        boolean checkDeadlock = config.getAttribute(IModelConfigurationConstants.MODEL_CORRECTNESS_CHECK_DEADLOCK,
                IModelConfigurationDefaults.MODEL_CORRECTNESS_CHECK_DEADLOCK_DEFAULT);
        if (checkDeadlock)
        {
            arguments.add("-deadlock");
        }

        boolean runAsModelCheck = config.getAttribute(IModelConfigurationConstants.LAUNCH_MC_MODE,
                IModelConfigurationDefaults.LAUNCH_MC_MODE_DEFAULT);
        if (runAsModelCheck)
        {
            // look for advanced model checking parameters
            boolean isDepthFirst = config.getAttribute(IModelConfigurationConstants.LAUNCH_DFID_MODE,
                    IModelConfigurationDefaults.LAUNCH_DFID_MODE_DEFAULT);
            if (isDepthFirst)
            {
                // for depth-first run, look for the depth
                int dfidDepth = config.getAttribute(IModelConfigurationConstants.LAUNCH_DFID_DEPTH,
                        IModelConfigurationDefaults.LAUNCH_DFID_DEPTH_DEFAULT);
                arguments.add("-dfid");
                arguments.add(String.valueOf(dfidDepth));
            }
        } else
        {
            arguments.add("-simulate");

            // look for advanced simulation parameters
            int traceDepth = config.getAttribute(IModelConfigurationConstants.LAUNCH_SIMU_DEPTH,
                    IModelConfigurationDefaults.LAUNCH_SIMU_DEPTH_DEFAULT);
            if (traceDepth != IModelConfigurationDefaults.LAUNCH_SIMU_DEPTH_DEFAULT)
            {
                arguments.add("-depth");
                arguments.add(String.valueOf(traceDepth));
            }

            int aril = config.getAttribute(IModelConfigurationConstants.LAUNCH_SIMU_ARIL,
                    IModelConfigurationDefaults.LAUNCH_SIMU_ARIL_DEFAULT);
            int seed = config.getAttribute(IModelConfigurationConstants.LAUNCH_SIMU_SEED,
                    IModelConfigurationDefaults.LAUNCH_SIMU_SEED_DEFAULT);
            if (aril != IModelConfigurationDefaults.LAUNCH_SIMU_ARIL_DEFAULT)
            {
                arguments.add("-aril");
                arguments.add(String.valueOf(aril));
            }
            if (seed != IModelConfigurationDefaults.LAUNCH_SIMU_SEED_DEFAULT)
            {
                arguments.add("-seed");
                arguments.add(String.valueOf(seed));
            }
        }
        
        // recover from checkpoint
        boolean recover = config.getAttribute(IModelConfigurationConstants.LAUNCH_RECOVER, IModelConfigurationDefaults.LAUNCH_RECOVER_DEFAULT);
        if (recover) 
        {
            IResource[] checkpoints = ModelHelper.getCheckpoints(config);
            if (checkpoints.length > 0) 
            {
                arguments.add("-recover");
                arguments.add(checkpoints[0].getName());
            }
        } 
        
        
        arguments.add("-config");
        arguments.add(cfgFile.getName()); // configuration file
        arguments.add("-coverage");
        arguments.add(String.valueOf(0.1)); // coverage 0.1 hour
        arguments.add("-workers");
        arguments.add(String.valueOf(workers)); // number of workers
        // arguments.add("-debug"); // debugging only
        arguments.add("-tool"); // run in tool mode
        arguments.add("-metadir");
        arguments.add(launchDir.getLocation().toOSString()); // running in directory
        arguments.add(ResourceHelper.getModuleName(rootModule)); // name of the module to check

        return (String[]) arguments.toArray(new String[arguments.size()]);
    }

    /**
     * Sets the number of workers
     * @param workers number of threads to be run in parallel
     */
    public void setWorkers(int workers)
    {
        this.workers = workers;
    }

    protected Action getJobCompletedAction()
    {
        return new Action("View job results") {
            public void run()
            {
                // TODO
                System.out.println("Results viewed");
            }
        };
    }

    /**
     * The run method
     */
    protected abstract IStatus run(IProgressMonitor monitor);

    /**
     * Checks if TLC is still running
     * @return true, if TLC is still running
     */
    public abstract boolean checkAndSleep();

    /**
     * Matches the spec (by name) or generic to the AllJobMatcher
     */
    public boolean belongsTo(Object family)
    {
        if (family != null)
        {
            if (family instanceof ILaunchConfiguration) 
            {
                return (this.launch.getLaunchConfiguration().contentsEqual((ILaunchConfiguration) family)); 
            } else if (family instanceof Spec)
            {
                Spec spec = (Spec) family;
                return (spec.getName().equals(this.specName));
            } else if (family instanceof AllJobMatcher)
            {
                return true;
            }
        }
        return false;
    }

}