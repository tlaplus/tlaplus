package org.lamport.tla.toolbox.tool.tlc.job;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
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

        monitor.beginTask("Starting", IProgressMonitor.UNKNOWN);

        // classpath
        String[] classPath = new String[]{ToolboxHandle.getTLAToolsClasspath().toOSString()};
        
        // full-qualified class name of the main class
        String mainClassFQCN = TLC.class.getName(); //SANY.class.getName()
        // String mainClassFQCN = SANY.class.getName();

        // arguments
        // String[] args = new String[] { ResourceHelper.getModuleName(rootModule) }; 
        String[] args = new String[] { "-config", cfgFile.getName(),
                // "-coverage", "0.1",
                "-workers", "" + workers, 
                //"-debug", 
                "-metadir", projectDir.getLocation().toOSString(),
                ResourceHelper.getModuleName(rootModule) };
        
        String workingDir = ResourceHelper.getParentDirName(rootModule);
        
        // using -D to pass the System property of the location of standard modules
        String[] vmArgs = new String[]{ "-DTLA-Library=" + ToolboxHandle.getModulesClasspath().toOSString()};

        
        // assemble the config
        VMRunnerConfiguration tlcConfig = new VMRunnerConfiguration(mainClassFQCN, classPath);
        tlcConfig.setProgramArguments(args);
        tlcConfig.setVMArguments(vmArgs);
        tlcConfig.setWorkingDirectory(workingDir);
        
        // get default VM (the same the toolbox is started with)
        IVMRunner runner = JavaRuntime.getDefaultVMInstall().getVMRunner(ILaunchManager.RUN_MODE);

        launch.setAttribute(DebugPlugin.ATTR_CAPTURE_OUTPUT, "true");

        try
        {
            runner.run(tlcConfig, launch, monitor);
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
            return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID, "Error launching TLC modle checker", e);
        }

        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
        IProcess[] processes = launchManager.getProcesses();
        IStreamListener consleListener = new IStreamListener() {
            public void streamAppended(String text, IStreamMonitor monitor)
            {
                print(text);
            }
        };

        for (int i = 0; i < processes.length; i++)
        {
            if (processes[i].getLaunch().equals(launch))
            {
                IProcess process = processes[i];
                process.getStreamsProxy().getOutputStreamMonitor().addListener(consleListener);
                process.getStreamsProxy().getErrorStreamMonitor().addListener(consleListener);
            }
        }

        monitor.done();
        return Status.OK_STATUS;
    }
}
