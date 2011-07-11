package org.lamport.tla.toolbox.tool.tlc.job;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tlc2.tool.distributed.TLCServer;

/**
 * Starts the distributed TLCServer inside the Toolbox 
 */
public class DistributedTLCJob extends TLCProcessJob {

	public DistributedTLCJob(String specName, String modelName, ILaunch launch, int numberOfWorkers) {
		super(specName, modelName, launch, numberOfWorkers);
	}
	
    /**
     * Removes non matching arguments from super class
     * @throws CoreException 
     */
	protected String[] constructProgramArguments() throws CoreException {
		final String userDir = launchDir.getLocation().toOSString();
		final String specFile = ResourceHelper.getModuleName(rootModule);
        
		final String[] args = new String[2];
		args[0] = userDir + File.separator + specFile;
		args[1] = "-tool";
        return args;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.job.TLCProcessJob#getAdditionalVMArgs()
	 */
	protected List<String> getAdditionalVMArgs() throws CoreException {
		final ILaunchConfiguration launchConfig = launch.getLaunchConfiguration();
		
		final String vmArgs = launchConfig.getAttribute(LAUNCH_DISTRIBUTED_ARGS, (String) null);
		if(vmArgs != null) {
			return sanitizeString(vmArgs);
		}

		// no args given
		return new ArrayList<String>(0);
	}
	
	/**
	 * @param vmArgs may look like " -Djava.rmi.foo=bar  -Djava.tralla=avalue  "
	 * @return a {@link List} with ["-Djava.rmi.foo=bar", "-Djava.tralla=avlue"]
	 */
	private List<String> sanitizeString(final String vmArgs) {
		final String[] strings = vmArgs.split(" ");
		final List<String> results = new ArrayList<String>(strings.length);
		for (int i = 0; i < strings.length; i++) {
			final String string = strings[i];
			if(!"".equals(string) && !" ".equals(string)) {
				results.add(string.trim());
			}
			// additional sanity checks could go here, but the nested process will report errors anyway
		}
		return results;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.job.TLCProcessJob#getMainClass()
	 */
	protected Class getMainClass() {
		return TLCServer.class;
	}
}
