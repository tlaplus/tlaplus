package org.lamport.tla.toolbox.tool.tlc.job;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.debug.core.IStreamListener;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.debug.core.model.IStreamMonitor;
import org.eclipse.jdt.launching.IVMRunner;
import org.eclipse.jdt.launching.JavaRuntime;
import org.eclipse.jdt.launching.VMRunnerConfiguration;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tlc2.TLC;

/**
 * A job to launch TLC as a separate process
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCProcessJob extends TLCJob
{
    private IProcess process = null;
    private IStreamListener consleListener = new IStreamListener() {
        public void streamAppended(String text, IStreamMonitor monitor)
        {
            print(text);
        }
    };

    
    /**
     * @param name
     */
    public TLCProcessJob(String specName, String modelName, ILaunch launch)
    {
        super(specName, modelName, launch);
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

            // init the console
            initConsole();

            // step 1
            monitor.worked(STEP);
            monitor.subTask("Preparing the TLC Launch");

            // classpath
            String[] classPath = new String[] { ToolboxHandle.getTLAToolsClasspath().toOSString() };

            // full-qualified class name of the main class
            String mainClassFQCN = TLC.class.getName();
            // String mainClassFQCN = SANY.class.getName();

            // arguments
            // String[] args = new String[] { ResourceHelper.getModuleName(rootModule) };
            String[] args = new String[] { "-config", cfgFile.getName(), // configuration file
                    "-coverage", "0.1", // coverage
                    "-workers", "" + workers, // number of workers
                    // "-debug",
                    "-metadir", launchDir.getLocation().toOSString(), // running in directory
                    ResourceHelper.getModuleName(rootModule) // name of the module to check
            };

            String workingDir = ResourceHelper.getParentDirName(rootModule);

            // using -D to pass the System property of the location of standard modules
            String[] vmArgs = new String[] { "-DTLA-Library=" + ToolboxHandle.getModulesClasspath().toOSString() };

            // assemble the config
            VMRunnerConfiguration tlcConfig = new VMRunnerConfiguration(mainClassFQCN, classPath);
            tlcConfig.setProgramArguments(args);
            tlcConfig.setVMArguments(vmArgs);
            tlcConfig.setWorkingDirectory(workingDir);

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
            } catch (CoreException e)
            {
                return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID, "Error launching TLC modle checker", e);
            }

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

                process.getStreamsProxy().getOutputStreamMonitor().addListener(consleListener);
                process.getStreamsProxy().getErrorStreamMonitor().addListener(consleListener);

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
                            switch (e.getStatus().getCode())
                            {
                            case DebugException.TARGET_REQUEST_FAILED:
                            case DebugException.NOT_SUPPORTED:
                            default:
                                return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID, "Error terminating the running TLC instance. This is a bug. Make sure to exit the toolbox.");
                            }
                        } 

                        // abnormal termination
                        return Status.CANCEL_STATUS;
                    }
                }

                // step 6
                monitor.worked(STEP);
                monitor.subTask("Model checking finished.");

                // handle finish
                doFinish();

                return Status.OK_STATUS;

            } else
            {
                // process not found
                return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID, "Error launching TLC, the launched process cound not be found");
            }

        } finally
        {
            // make sure to complete the monitor
            monitor.done();
        }
    }

    /**
     * @see {@link TLCJob#checkAndSleep()}
     */
    public boolean checkAndSleep()
    {
        try
        {
            // go sleep
            Thread.sleep(TIMEOUT);

        } catch (InterruptedException e)
        {
            // nothing to do
            // e.printStackTrace();
        }
        // return true if the TLC is still calculating
        return (!process.isTerminated());
    }
    
    /**
     * Retrieves a process to a given ILaunch
     * @param launch
     * @return
     */
    public static IProcess findProcessForLaunch(ILaunch launch)
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
}
