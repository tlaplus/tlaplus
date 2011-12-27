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
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.jdt.launching.IVMRunner;
import org.eclipse.jdt.launching.JavaRuntime;
import org.eclipse.jdt.launching.VMRunnerConfiguration;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.launch.TraceExplorerDelegate;
import org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink;
import org.lamport.tla.toolbox.tool.tlc.output.internal.BroadcastStreamListener;
import org.lamport.tla.toolbox.tool.tlc.util.TLCRuntime;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tlc2.TLC;

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
			// classpath during toolbox development within Eclipse (will simply not
			// exist in packaged toolbox)
			final String devClasspath = runtimeClasspath + File.separator + "class";
			String[] classPath = new String[] { runtimeClasspath, devClasspath };

            // arguments
            String[] arguments = constructProgramArguments();

            // log output
            org.lamport.tla.toolbox.tool.tlc.TLCActivator.logDebug(
            		"TLC ARGUMENTS: " +
            		Arrays.toString(arguments));

            final List<String> vmArgs = new ArrayList<String>();

            // get max heap size as fraction from model editor
            final double maxHeapSize = launch.getLaunchConfiguration().getAttribute(LAUNCH_MAX_HEAP_SIZE, 50) / 100d;
			final TLCRuntime instance = TLCRuntime.getInstance();
			final long absolutePhysicalSystemMemory = instance.getAbsolutePhysicalSystemMemory(maxHeapSize);
			vmArgs.add("-Xmx" + absolutePhysicalSystemMemory + "m");

            // add remaining VM args
            vmArgs.addAll(getAdditionalVMArgs());

            // assemble the config
            VMRunnerConfiguration tlcConfig = new VMRunnerConfiguration(getMainClass().getName(), classPath);
            // tlcConfig.setProgramArguments(new String[] { ResourceHelper.getModuleName(rootModule) });
            tlcConfig.setProgramArguments(arguments);
            tlcConfig.setVMArguments((String[]) vmArgs.toArray(new String[vmArgs.size()]));
            tlcConfig.setWorkingDirectory(ResourceHelper.getParentDirName(rootModule));

            // get default VM (the same the toolbox is started with)
            IVMRunner runner = JavaRuntime.getDefaultVMInstall().getVMRunner(ILaunchManager.RUN_MODE);

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
                while (checkAndSleep())
                {
                    // check the cancellation status
                    if (monitor.isCanceled())
                    {
                        // cancel the TLC
                        try
                        {
                            process.terminate();
                        } catch (DebugException e)
                        {
                            // react on the status code
                            switch (e.getStatus().getCode()) {
                            case DebugException.TARGET_REQUEST_FAILED:
                            case DebugException.NOT_SUPPORTED:
                            default:
                                return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                                        "Error terminating the running TLC instance. This is a bug. Make sure to exit the toolbox.");
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
		return new ArrayList<String>();
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
