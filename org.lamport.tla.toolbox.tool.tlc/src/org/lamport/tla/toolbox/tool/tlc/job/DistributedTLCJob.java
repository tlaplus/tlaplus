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

	private static final List<String> WHITELIST = new ArrayList<String>();
	private static final List<String> WHITELIST_WITH_ARG = new ArrayList<String>();
	// take from tlc2.tool.distributed.TLCApp.create(String[])
	static {
		WHITELIST.add("-deadlock");
		WHITELIST.add("-terse");
		WHITELIST.add("-nowarning");
		
		WHITELIST_WITH_ARG.add("-checkpoint");
// Temporarily removed due to http://bugzilla.tlaplus.net/show_bug.cgi?id=212
//		WHITELIST_WITH_ARG.add("-coverage");
		WHITELIST_WITH_ARG.add("-fp");
		WHITELIST_WITH_ARG.add("-recover");
		WHITELIST_WITH_ARG.add("-metadir");
	}
	
	public DistributedTLCJob(String specName, String modelName, ILaunch launch, int numberOfWorkers) {
		super(specName, modelName, launch, numberOfWorkers);
	}
	
    /**
     * Removes non matching arguments from super class
     * @throws CoreException 
     */
	protected String[] constructProgramArguments() throws CoreException {
		final List<String> arguments = new ArrayList<String>();
		
		// filter super args to what is accepted by TLCServer/TLCApp
		final List<String> superArguments = Arrays.asList(super.constructProgramArguments());
		for (int i = 0; i < superArguments.size(); i++) {
			final String arg = superArguments.get(i);
			if(WHITELIST.contains(arg)) {
				arguments.add(arg);
			} else if(WHITELIST_WITH_ARG.contains(arg)) {
				arguments.add(arg);
				arguments.add(superArguments.get(++i));
			}
		}
		
		// local args
		final String userDir = launchDir.getLocation().toOSString();
		final String specFile = ResourceHelper.getModuleName(rootModule);
        
		arguments.add(userDir + File.separator + specFile);
		arguments.add("-tool");
        return arguments.toArray(new String[arguments.size()]);
	}
	
	protected List<String> getAdditionalVMArgs() throws CoreException {
		final List<String> additionalVMArgs = super.getAdditionalVMArgs();
		
		// distributed FPSet count
		final ILaunchConfiguration launchConfig = launch.getLaunchConfiguration();
		final int distributedFPSetCount = launchConfig.getAttribute(LAUNCH_DISTRIBUTED_FPSET_COUNT, 0);
		if (distributedFPSetCount > 0) {
			additionalVMArgs.add("-Dtlc2.tool.distributed.TLCServer.expectedFPSetCount=" + distributedFPSetCount);
		}
		
		// Inet Address to listen on
		final String iface = launchConfig.getAttribute(LAUNCH_DISTRIBUTED_INTERFACE, "");
		if (!"".equals(iface)) {
			additionalVMArgs.add("-Djava.rmi.server.hostname=" + iface);
		}
		
		return additionalVMArgs;
	}


	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.job.TLCProcessJob#getMainClass()
	 */
	protected Class getMainClass() {
		return TLCServer.class;
	}
}
