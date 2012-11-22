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
import org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink;
import org.lamport.tla.toolbox.tool.tlc.output.internal.BroadcastStreamListener;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tlc2.TLC;
import tlc2.tool.fp.FPSetFactory;
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
			final long absolutePhysicalSystemMemory = instance.getAbsolutePhysicalSystemMemory(maxHeapSize);

			// Set class name of FPSet (added by MAK on 07/31/2012)
			final String clazz = launch.getLaunchConfiguration().getAttribute(LAUNCH_FPSET_IMPL,
					FPSetFactory.getImplementationDefault());
			vmArgs.add("-D" + FPSetFactory.IMPL_PROPERTY + "=" + clazz);
			vmArgs.add(FPSetFactory.getVMArguments(clazz, absolutePhysicalSystemMemory));
			
            // add remaining VM args
            vmArgs.addAll(getAdditionalVMArgs());


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

                String modelFileName = launch.getLaunchConfiguration().getFile().getName();

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

                listener = new BroadcastStreamListener(modelFileName, kind);

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

}
