package org.lamport.tla.toolbox.tool.tlc.job;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
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

    /**
     * @param name
     */
    public TLCProcessJob(IResource rootModule, IResource cfgFile, IResource projectDir, ILaunch launch)
    {
        super(rootModule, cfgFile, projectDir, launch);
    }

    /* (non-Javadoc)
     * @see org.eclipse.core.runtime.jobs.Job#run(org.eclipse.core.runtime.IProgressMonitor)
     */
    protected IStatus run(IProgressMonitor monitor)
    {
        // init the console
        initConsole();

        monitor.beginTask("Running TLC model checker", IProgressMonitor.UNKNOWN);
        monitor.worked(STEP);

        monitor.subTask("Preparing the TLC Launch");
        // classpath
        String[] classPath = new String[] { ToolboxHandle.getTLAToolsClasspath().toOSString() };

        // full-qualified class name of the main class
        String mainClassFQCN = TLC.class.getName();
        // String mainClassFQCN = SANY.class.getName();

        // arguments
        // String[] args = new String[] { ResourceHelper.getModuleName(rootModule) };
        String[] args = new String[] { "-config", cfgFile.getName(),
        // "-coverage", "0.1",
                "-workers", "" + workers,
                // "-debug",
                "-metadir", projectDir.getLocation().toOSString(), ResourceHelper.getModuleName(rootModule) };

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

        monitor.subTask("Launching TLC");
        try
        {
            runner.run(tlcConfig, launch, monitor);
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
            return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID, "Error launching TLC modle checker", e);
        }
        monitor.worked(STEP);

        IStreamListener consleListener = new IStreamListener() {
            public void streamAppended(String text, IStreamMonitor monitor)
            {
                print(text);
            }
        };

        // find the process
        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
        IProcess[] processes = launchManager.getProcesses();
        for (int i = 0; i < processes.length; i++)
        {
            if (processes[i].getLaunch().equals(launch))
            {
                this.process = processes[i];
                break;
            }
        }

        // process found
        if (process != null)
        {
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
                        // TODO Auto-generated catch block
                        e.printStackTrace();
                    }

                    // abnormal termination
                    return Status.CANCEL_STATUS;
                }
                monitor.worked(STEP);
            }
            
            monitor.worked(STEP);
            
            // handle finish
            doFinish();

            return Status.OK_STATUS;

        } else
        {
            // TODO process not found
            return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID, "Error launching TLC");
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
            e.printStackTrace();
        }
        // return true if the TLC is still calculating
        return (!process.isTerminated());
    }
}
