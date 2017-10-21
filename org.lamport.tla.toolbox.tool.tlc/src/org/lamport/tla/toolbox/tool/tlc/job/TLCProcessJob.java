package org.lamport.tla.toolbox.tool.tlc.job;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.jdt.launching.IVMInstall;
import org.eclipse.jdt.launching.IVMRunner;
import org.eclipse.jdt.launching.VMRunnerConfiguration;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.launch.TraceExplorerDelegate;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink;
import org.lamport.tla.toolbox.tool.tlc.output.internal.BroadcastStreamListener;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tlc2.TLC;
import tlc2.tool.fp.FPSetFactory;
import tlc2.tool.fp.OffHeapDiskFPSet;
import util.TLCRuntime;

/**
 * A job to launch TLC as a separate process
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCProcessJob extends TLCJob
{
    protected IProcess process = null;
    private BroadcastStreamListener listener = null;

    /**
     * The tlc start time in milliseconds as given
     * by {@link System#currentTimeMillis()}.
     */
    private long tlcStartTime;
    /**
     * The tlc end time in milliseconds as given
     * by {@link System#currentTimeMillis()}.
     */
    private long tlcEndTime;

    /**
     * Constructs a process job
     * @param workers 
     * @param name
     */
    public TLCProcessJob(String specName, String modelName, ILaunch launch, int workers)
    {
        super(specName, modelName, launch, workers);
    }

    /* (non-Javadoc)
     * @see org.eclipse.core.runtime.jobs.Job#run(org.eclipse.core.runtime.IProgressMonitor)
     */
    protected IStatus run(IProgressMonitor monitor)
    {
        try
        {

            // start the monitor ( we don't know the )
            monitor.beginTask("Running TLC model checker", IProgressMonitor.UNKNOWN);

            // step 1
            monitor.worked(STEP);
            monitor.subTask("Preparing the TLC Launch");

            // classpath
            final String runtimeClasspath = ToolboxHandle.getTLAToolsClasspath().toOSString();
			// Add 3rd party libraries to classpath. Star acts as wildcard
			// picking up all .jar files (added by MAK on 07/31/2012)
			final String libClasspath = runtimeClasspath + File.separator + "lib" + File.separator + "*";
			// classpath during toolbox development within Eclipse (will simply not
			// exist in packaged toolbox)
			final String devClasspath = runtimeClasspath + File.separator + "class";
			String[] classPath = new String[] { runtimeClasspath, libClasspath, devClasspath };

            // arguments
            String[] arguments = constructProgramArguments();

            // log output
			TLCActivator
					.logInfo("TLC ARGUMENTS: " + Arrays.toString(arguments));

            final List<String> vmArgs = new ArrayList<String>();

            // get max heap size as fraction from model editor
            final double maxHeapSize = launch.getLaunchConfiguration().getAttribute(LAUNCH_MAX_HEAP_SIZE, 50) / 100d;
			final TLCRuntime instance = TLCRuntime.getInstance();
			long absolutePhysicalSystemMemory = instance.getAbsolutePhysicalSystemMemory(maxHeapSize);

			// Get class name of the user selected FPSet. If it is unset, try and load the
			// OffHeapDiskFPSet (which might not be supported). In unsupported, revert to
			// TLC's default set.
			// If the user happened to select OffHeapDiskFPSet, the -XX:MaxDirectMemorySize
			// is set by getVMArguments.
			final String clazz = launch.getLaunchConfiguration().getAttribute(LAUNCH_FPSET_IMPL, (String) null);
			if (clazz == null || clazz.equals(OffHeapDiskFPSet.class.getName())) {
				if (OffHeapDiskFPSet.isSupported()) {
					// ...good, can use lock-free/scalabe fpset, but need to divide assigned memory
					// into JVM heap and non-heap/off-heap memory. Let's assign 2/3 to the off-heap
					// FPSet.
					final long offheapMemory = (long) (absolutePhysicalSystemMemory * 0.6666d);
					vmArgs.add(FPSetFactory.getVMArguments(OffHeapDiskFPSet.class.getName(), offheapMemory));

					// Rest goes to the heap (state queue/...).
					vmArgs.add(FPSetFactory.getVMArguments(FPSetFactory.getImplementationDefault(),
							absolutePhysicalSystemMemory - offheapMemory));
					
					vmArgs.add("-D" + FPSetFactory.IMPL_PROPERTY + "=" + OffHeapDiskFPSet.class.getName());
				} else {
					// Off-heap fpset couldn't be loaded. Use default fpset and assign all memory to
					// heap memory.
					vmArgs.add(FPSetFactory.getVMArguments(FPSetFactory.getImplementationDefault(),
							absolutePhysicalSystemMemory));
					vmArgs.add("-D" + FPSetFactory.IMPL_PROPERTY + "=" + FPSetFactory.getImplementationDefault());
				}
			} else {
				vmArgs.add(FPSetFactory.getVMArguments(clazz, absolutePhysicalSystemMemory));
				vmArgs.add("-D" + FPSetFactory.IMPL_PROPERTY + "=" + clazz);
			}
			
            // add remaining VM args
            vmArgs.addAll(getAdditionalVMArgs());
            
            // have the TLC launch pause and wait for contact from a remote debugger before continuing
            //		should the Toolbox instance have been launched with an appropriate environment variable
            //		set to any value
            if (System.getenv("LAUNCH_TLC_IN_DEBUG") != null) {
	        		vmArgs.add("-Xdebug");
	        		vmArgs.add("-Xrunjdwp:transport=dt_socket,address=9321,server=y");
            }

            // assemble the config
            VMRunnerConfiguration tlcConfig = new VMRunnerConfiguration(getMainClass().getName(), classPath);
            // tlcConfig.setProgramArguments(new String[] { ResourceHelper.getModuleName(rootModule) });
            tlcConfig.setProgramArguments(arguments);
            tlcConfig.setVMArguments((String[]) vmArgs.toArray(new String[vmArgs.size()]));
            tlcConfig.setWorkingDirectory(ResourceHelper.getParentDirName(rootModule));
            // Following added for testing by LL on 6 Jul 2012
            TLCActivator.logInfo("JAVA VM ARGUMENTS: " + Arrays.toString(tlcConfig.getVMArguments()));             
            final IVMInstall vmInstall = getVMInstall();
            TLCActivator.logInfo("Nested JVM used for model checker is: "
					+ vmInstall.getInstallLocation());
            
			final IVMRunner runner = vmInstall.getVMRunner(ILaunchManager.RUN_MODE);

            launch.setAttribute(DebugPlugin.ATTR_CAPTURE_OUTPUT, "true");

            // step 2
            monitor.worked(STEP);
            monitor.subTask("Launching TLC");

            try
            {
                // step 3
                runner.run(tlcConfig, launch, new SubProgressMonitor(monitor, STEP));
                tlcStartTime = System.currentTimeMillis();
            } catch (CoreException e)
            {
                return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID, "Error launching TLC modle checker", e);
            }

            // find the running process
            this.process = findProcessForLaunch(launch);

            // step 4
            monitor.worked(STEP);
            monitor.subTask("Connecting to running instance");

            // process found
            if (this.process != null)
            {
                // step 5
                monitor.worked(STEP);
                monitor.subTask("Model checking...");

                // register the broadcasting listener

                final Model model = launch.getLaunchConfiguration().getAdapter(Model.class);

                /*
                 * If TLC is being run for model checking then the stream kind passed to
                 * BroadcastStreamListener (second argument) is IProcessOutputSink.TYPE_OUT.
                 * If TLC is being run for trace exploration, then it is
                 * IProcessOutputSink.TYPE_TRACE_EXPLORE.
                 */

                int kind = IProcessOutputSink.TYPE_OUT;

                if (launch.getLaunchMode().equals(TraceExplorerDelegate.MODE_TRACE_EXPLORE))
                {
                    kind = IProcessOutputSink.TYPE_TRACE_EXPLORE;
                }

                listener = new BroadcastStreamListener(model, kind);

                process.getStreamsProxy().getOutputStreamMonitor().addListener(listener);
                process.getStreamsProxy().getErrorStreamMonitor().addListener(listener);

                // loop until the process is terminated
				while (checkAndSleep()) {
					// check the cancellation status
					if (monitor.isCanceled()) {
						// cancel the TLC
						try {
							process.terminate();
						} catch (DebugException e) {
							// react on the status code
							switch (e.getStatus().getCode()) {
							case DebugException.TARGET_REQUEST_FAILED:
							case DebugException.NOT_SUPPORTED:
							default:
								// MAK 11/2012: Remove e.getStatus().getCode()
								// and e (throwable) once Chris' problem
								// cancellation has been diagnosed
								return new Status(
										IStatus.ERROR,
										TLCActivator.PLUGIN_ID,
										e.getStatus().getCode(),
										"Error terminating the running TLC instance. This is a bug. Make sure to exit the toolbox.",
										e);
							}
						}

						// Wait for the process to terminate. Otherwise, it
						// opens the door to a race condition in
						// org.lamport.tla.toolbox.tool.tlc.model.Model such
						// that isRunning returns true querying the Launch (which
						// is directly connected to the Process instance), even
						// after the outer TLCProcessJob's JobListener
						// ...launch.TLCModelLaunchDelegate.TLCJobChangeListener
						// has setRunning(false). 
						int i = 0;
						while (!process.isTerminated() || i++ >= 10) {
							try {
								Thread.sleep(100L);
							} catch (InterruptedException e) {
								e.printStackTrace();
								return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
										"Error waiting for process termianation.", e);
							}
						}
						if (!process.isTerminated()) {
							TLCActivator.logInfo(
									"TLC process failed to terminate within expected time window. Expect Toolbox to show an incorrect model state.");
						}
						
						// abnormal termination
						tlcEndTime = System.currentTimeMillis();
						return Status.CANCEL_STATUS;
					}
				}

                // step 6
                monitor.worked(STEP);
                monitor.subTask("Model checking finished.");

                // handle finish
                doFinish();

                tlcEndTime = System.currentTimeMillis();

                return Status.OK_STATUS;

            } else
            {
                // process not found
                return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                        "Error launching TLC, the launched process cound not be found");
            }

        } catch (CoreException e)
        {
            return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID, "Error reading model parameters", e);
        } finally
        {
            // send the notification about completion
            if (listener != null)
            {
                listener.streamClosed();
                // remove this listener from the stream to avoid memory leak
                if (process != null && process.getStreamsProxy() != null)
                {
                    if (process.getStreamsProxy().getOutputStreamMonitor() != null)
                    {
                        process.getStreamsProxy().getOutputStreamMonitor().removeListener(listener);
                    }
                    if (process.getStreamsProxy().getErrorStreamMonitor() != null)
                    {
                        process.getStreamsProxy().getErrorStreamMonitor().removeListener(listener);
                    }
                }
            }
            // make sure to complete the monitor
            monitor.done();
        }
    }

	/**
	 * @return A list of additional vm arguments
	 */
	protected List<String> getAdditionalVMArgs() throws CoreException {
		final List<String> result = new ArrayList<String>(0);

		/*
		 * Allow access to the java.activation module on Java9 
		 * https://bugs.eclipse.org/493761
		 * http://download.java.net/java/jdk9/docs/api/java.activation-summary.html
		 * 
		 * This is needed by MailSender.java.
		 */
		result.add("--add-modules=java.activation");
		// Have < Java9 ignore --add-modules=java.activation flag
		result.add("-XX:+IgnoreUnrecognizedVMOptions");
		
		// Library Path
		final Spec spec = Activator.getSpecManager().getSpecByName(specName);
		final String tlaLibraryPathAsVMArg = spec.getTLALibraryPathAsVMArg();
		if (!"".equals(tlaLibraryPathAsVMArg)) {
			result.add(tlaLibraryPathAsVMArg);
		}

		// JVM arguments/system properties
		final ILaunchConfiguration launchConfig = launch.getLaunchConfiguration();
		final String vmArgs = launchConfig.getAttribute(LAUNCH_JVM_ARGS, (String) null);
		if(vmArgs != null) {
			result.addAll(sanitizeString(vmArgs));
		}

		return result;
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

	@SuppressWarnings("rawtypes")
	protected Class getMainClass() {
		return TLC.class;
	}

    protected boolean checkCondition() {
        // return true if the TLC is still calculating
    	return !process.isTerminated();
    }
    
    /**
     * Retrieves a process to a given ILaunch
     * @param launch
     * @return
     */
    private static IProcess findProcessForLaunch(ILaunch launch)
    {
        // find the process
        IProcess[] processes = DebugPlugin.getDefault().getLaunchManager().getProcesses();
        for (int i = 0; i < processes.length; i++)
        {
            if (processes[i].getLaunch().equals(launch))
            {
                return processes[i];
            }
        }
        return null;
    }

    /**
     * Returns the tlc start time in milliseconds as given
     * by {@link System#currentTimeMillis()}.
     * @return
     */
    public long getTlcStartTime()
    {
        return tlcStartTime;
    }

    /**
     * Returns the tlc end time in milliseconds as given
     * by {@link System#currentTimeMillis()}.
     * @return
     */
    public long getTlcEndTime()
    {
        return tlcEndTime;
    }

	/**
	 * @return The processee's exit/return value or -1 if unknown.
	 */
    public int getExitValue() {
    	if (this.process != null) {
    		try {
    			return this.process.getExitValue();
    		} catch (DebugException shouldNotHappen) {
    			shouldNotHappen.printStackTrace();
    		}
    	}
    	return -1;
    }
}
