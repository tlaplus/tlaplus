package org.lamport.tla.toolbox.tool.tlc.job;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.action.Action;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.launch.TraceExplorerDelegate;
import org.lamport.tla.toolbox.tool.tlc.result.IResultPresenter;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.ToolboxJob;

import tlc2.TLCGlobals;

/**
 * Abstract TLC job
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class TLCJob extends AbstractJob implements IModelConfigurationConstants, IModelConfigurationDefaults
{

    /**
     * Job family identifier for all org.lamport toolbox jobs
     */
    public static final String AllJobsMatcher = ToolboxJob.FAMILY;

    protected static final int STEP = 30;
    /*
     * Number of minutes between printing of coverage data.
     */
    private static final int COVERAGE_INTERVAL = 3;
    
    /*
     * Number of minutes between checkpoints.  It was changed from 20 or 30 to 3,
     * apparently by Simon Z.  Changed to 15 by LL for 10 Apr 2012 release
     * 
     */
    private static final int CHECKPOINT_INTERVAL = 15 ;  
    
    protected long timeout = 1000L;
    protected IFile rootModule;
    protected IFile cfgFile;
    protected IFile outFile;
    protected IFolder launchDir;
    protected int workers = 1;
    protected ILaunch launch;
    protected String modelName;
    protected final String specName;

    protected boolean appendConsole = true;

    public TLCJob(String specName, String modelName, ILaunch launch)
    {
    	this(specName, modelName, launch, 1);
    }
    
    /**
     * Creates a TLC job for a given spec and model
     * @param workers2 
     * @param rootModule
     * @param cfgFile
     * @param launchDir
     * @param workers number of threads to be run in parallel
     */
    public TLCJob(String specName, String modelName, ILaunch launch, int workers)
    {
        super("TLC run for " + modelName);
        this.specName = specName;
        this.modelName = modelName;
        this.workers = workers;

        IProject project = ResourceHelper.getProject(specName);
        Assert.isNotNull(project, "Error accessing the spec project " + specName);

        this.launchDir = project.getFolder(modelName);
        Assert.isNotNull(this.launchDir, "Error accessing the model folder " + modelName);

        this.launch = launch;

        if (launch.getLaunchMode().equals(TraceExplorerDelegate.MODE_TRACE_EXPLORE))
        {
            this.rootModule = this.launchDir.getFile(ModelHelper.TE_FILE_TLA);
            this.cfgFile = this.launchDir.getFile(ModelHelper.TE_FILE_CFG);
            this.outFile = this.launchDir.getFile(ModelHelper.TE_FILE_OUT);
        } else
        {
            this.rootModule = this.launchDir.getFile(ModelHelper.FILE_TLA);
            this.cfgFile = this.launchDir.getFile(ModelHelper.FILE_CFG);
            this.outFile = this.launchDir.getFile(ModelHelper.FILE_OUT);
        }
    }

    /**
     * Reads the model parameters and constructs the corresponding command line arguments
     * @return string array with arguments
     * @throws CoreException
     */
    protected String[] constructProgramArguments() throws CoreException
    {
    	Map<String, String> arguments = new HashMap<String, String>();
        ILaunchConfiguration config = launch.getLaunchConfiguration();

        // deadlock
        boolean checkDeadlock = config.getAttribute(IModelConfigurationConstants.MODEL_CORRECTNESS_CHECK_DEADLOCK,
                IModelConfigurationDefaults.MODEL_CORRECTNESS_CHECK_DEADLOCK_DEFAULT);
        if (!checkDeadlock) /* "!" added by LL on 22 Aug 2009 */
        {
            arguments.put("-deadlock", null);
        }

        // adjust checkpointing
       	arguments.put("-checkpoint", String.valueOf(CHECKPOINT_INTERVAL));

        boolean hasSpec = config.getAttribute(MODEL_BEHAVIOR_SPEC_TYPE, MODEL_BEHAVIOR_TYPE_DEFAULT) != IModelConfigurationDefaults.MODEL_BEHAVIOR_TYPE_NO_SPEC;

        if (hasSpec)
        {
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
                    arguments.put("-dfid", String.valueOf(dfidDepth));
                }
            } else
            {
                arguments.put("-simulate", null);

                // look for advanced simulation parameters
                int traceDepth = config.getAttribute(IModelConfigurationConstants.LAUNCH_SIMU_DEPTH,
                        IModelConfigurationDefaults.LAUNCH_SIMU_DEPTH_DEFAULT);
                if (traceDepth != IModelConfigurationDefaults.LAUNCH_SIMU_DEPTH_DEFAULT)
                {
                    arguments.put("-depth", String.valueOf(traceDepth));
                }

                int aril = config.getAttribute(IModelConfigurationConstants.LAUNCH_SIMU_ARIL,
                        IModelConfigurationDefaults.LAUNCH_SIMU_ARIL_DEFAULT);
                int seed = config.getAttribute(IModelConfigurationConstants.LAUNCH_SIMU_SEED,
                        IModelConfigurationDefaults.LAUNCH_SIMU_SEED_DEFAULT);
                if (aril != IModelConfigurationDefaults.LAUNCH_SIMU_ARIL_DEFAULT)
                {
                    arguments.put("-aril", String.valueOf(aril));
                }
                if (seed != IModelConfigurationDefaults.LAUNCH_SIMU_SEED_DEFAULT)
                {
                    arguments.put("-seed", String.valueOf(seed));
                }
            }
        }

        // recover from checkpoint
        if (hasSpec)
        {
            boolean recover = config.getAttribute(IModelConfigurationConstants.LAUNCH_RECOVER,
                    IModelConfigurationDefaults.LAUNCH_RECOVER_DEFAULT);
            if (recover)
            {
                IResource[] checkpoints = ModelHelper.getCheckpoints(config, false);
                if (checkpoints.length > 0)
                {
                    arguments.put("-recover", checkpoints[0].getName());
                }
            }
        }
        
        // fpBits
        int fpBits = launch.getLaunchConfiguration().getAttribute(LAUNCH_FPBITS, -1);
        if(fpBits >= 0) {
        	arguments.put("-fpbits", String.valueOf(fpBits));
        }
        
        // fp seed offset (decrease by one to map from [1, 64] interval to [0, 63] array address
        final int fpSeedOffset = launch.getLaunchConfiguration().getAttribute(LAUNCH_FP_INDEX, LAUNCH_FP_INDEX_DEFAULT);
        arguments.put("-fp", String.valueOf(fpSeedOffset - 1));
        
        // add maxSetSize argument if not equal to the default
        // code added by LL on 9 Mar 2012
        final int maxSetSize = launch.getLaunchConfiguration().getAttribute(
                LAUNCH_MAXSETSIZE, TLCGlobals.setBound);
        if (maxSetSize != TLCGlobals.setBound) {
            arguments.put("-maxSetSize", String.valueOf(maxSetSize));
        }
        
        arguments.put("-config", cfgFile.getName()); // configuration file

        // Should not add a coverage option only if TLC is being run
        // without a spec. This change added 10 Sep 2009 by LL & DR
        if (config.getAttribute(MODEL_BEHAVIOR_SPEC_TYPE, MODEL_BEHAVIOR_TYPE_DEFAULT) != MODEL_BEHAVIOR_TYPE_NO_SPEC)
        {
        	// coverage 0.1 hour
        	arguments.put("-coverage", String.valueOf(COVERAGE_INTERVAL)); 
        }
        
        // number of workers
        arguments.put("-workers", String.valueOf(workers));
        
        // debugging only
        //arguments.put("-debug", null); 
        
        // run in tool mode
        arguments.put("-tool", null);
        
        // running in directory
        arguments.put("-metadir", launchDir.getLocation().toOSString()); 
        
		// name of the module to check
        arguments.put(ResourceHelper.getModuleName(rootModule), null); 

        // Replace any of the above parameters if explicitly given as extra TLC parameters
		final ILaunchConfiguration launchConfig = launch.getLaunchConfiguration();
		final String tlcParameters = launchConfig.getAttribute(LAUNCH_TLC_PARAMETERS, (String) null);
		arguments.putAll(parseTLCParameters(tlcParameters));

        // Convert Map<String, String> of arguments to String[]
		final List<String> res = new ArrayList<String>(arguments.size());
		final Iterator<Entry<String, String>> iterator = arguments.entrySet().iterator();
		while(iterator.hasNext()) {
			Entry<String, String> elem = iterator.next();
			res.add(elem.getKey());
			if (elem.getValue() != null) {
				res.add(elem.getValue());
			}
		}
        return (String[]) res.toArray(new String[arguments.size()]);
    }

	/**
     * Returns the action that tells all registered result
     * presenters to show results. Result presenters are registered
     * using the extension point {@link IResultPresenter#EXTENSION_ID}.
     */
    protected Action getJobCompletedAction()
    {
        return new Action("View job results") {
            public void run()
            {
                IResultPresenter[] registeredResultPresenters = getRegisteredResultPresenters();
                for (int i = 0; i < registeredResultPresenters.length; i++)
                {
                    registeredResultPresenters[i].showResults(launch);
                }
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
    protected boolean checkAndSleep()
    {
        try
        {
            // go sleep
            Thread.sleep(timeout);

        } catch (InterruptedException e)
        {
            e.printStackTrace();
        }
        // return true if the TLC is still calculating
        return checkCondition();
    }
    
    protected abstract boolean checkCondition();

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
            } else if (AllJobsMatcher.equals(family))
            {
                return true;
            }
        }
        return false;
    }

    /**
     * Retrieves all presenter of TLC job results
     * @return 
     */
    protected static IResultPresenter[] getRegisteredResultPresenters()
    {
        IConfigurationElement[] decls = Platform.getExtensionRegistry().getConfigurationElementsFor(
                IResultPresenter.EXTENSION_ID);

        Vector<IResultPresenter> validExtensions = new Vector<IResultPresenter>();
        for (int i = 0; i < decls.length; i++)
        {
            try
            {
                IResultPresenter extension = (IResultPresenter) decls[i].createExecutableExtension("class");
                validExtensions.add(extension);
            } catch (CoreException e)
            {
                TLCActivator.getDefault().logError("Error instatiating the IResultPresenter extension", e);
            }
        }
        return validExtensions.toArray(new IResultPresenter[validExtensions.size()]);
    }

    /**
	 * Accepts a list like "-checkpoint 0 -workers 8 -tool" and creates a Map of
	 * "-checkpoint=0, -workers=8, -tool=null".<br>
	 * It does _not_ handle single non-command parameters like the name of the
	 * model file! This should generally be passed by the toolbox automatically.
	 * 
	 * @param tlcParameters
	 * @return
	 */
    private Map<String, String> parseTLCParameters(final String tlcParameters) {
    	if (tlcParameters == null || "".equals(tlcParameters)) {
    		return new HashMap<String, String>();
    	} else {
    		// use dash as a delimiter (prepend it later)
    		final String[] strings = tlcParameters.trim().split("-");
    		
    		final Map<String, String> res = new HashMap<String, String>(strings.length);
    		
    		for (int i = 0; i < strings.length; i++) {
    			if (!"".equals(strings[i])) {
    				String[] split = strings[i].split(" ");
    				if (split.length == 2) {
    					res.put("-" + split[0].trim(), split[1].trim());
    				} else {
    					res.put("-" + split[0].trim(), null);
    				}
    			}
			}
    		
    		return res;
    	}
	}
}