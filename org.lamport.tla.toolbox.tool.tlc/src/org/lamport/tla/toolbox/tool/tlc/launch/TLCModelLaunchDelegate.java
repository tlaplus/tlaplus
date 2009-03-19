package org.lamport.tla.toolbox.tool.tlc.launch;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.jobs.JobChangeAdapter;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.ILaunchConfigurationDelegate;
import org.eclipse.debug.core.model.LaunchConfigurationDelegate;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.job.AbstractJob;
import org.lamport.tla.toolbox.tool.tlc.job.TLCJob;

/**
 * Represents a launch delegate for TLC
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCModelLaunchDelegate extends LaunchConfigurationDelegate implements ILaunchConfigurationDelegate,
        IModelConfigurationConstants, IModelConfigurationDefaults
{
    public static final String LAUNCH_ID = "org.lamport.tla.toolbox.tool.tlc.modelCheck";
    public static final String MODE_MODELCHECK = "modelcheck";

    public void launch(ILaunchConfiguration config, String mode, ILaunch launch, IProgressMonitor monitor)
            throws CoreException
    {

        String specName = config.getAttribute(SPEC_NAME, EMPTY_STRING);
        String modelName = config.getAttribute(MODEL_NAME, EMPTY_STRING);

        System.out.println("Staring TLC on model " + modelName + " of spec " + specName + " in mode " + mode);

        
        String modelRootFilename = config.getAttribute(MODEL_ROOT_FILE, EMPTY_STRING);
        String configFilename = config.getAttribute(CONFIG_FILE, EMPTY_STRING);
        
        System.out.println("Model TLA file is: " + modelRootFilename);
        System.out.println("Model CFG file is: " + configFilename);
        
        
        // root file
        IResource rootModule = ToolboxHandle.getCurrentSpec().getProject().findMember(new Path(modelRootFilename).lastSegment());
        
        // config file
        IResource cfgFile = ToolboxHandle.getCurrentSpec().getProject().findMember(new Path(configFilename).lastSegment());

        
        
        // TODO modify CFG and TLA
        
        
        
        
        
        // construct TLC job
        AbstractJob job = new TLCJob(rootModule, cfgFile);
        job.addJobChangeListener(new JobChangeAdapter() {

            public void done(IJobChangeEvent event)
            {
                if (event.getResult().isOK())
                {
                    System.out.println("JOB Change Listener ------------ { Done }");
                } else
                {
                    System.out.println("JOB Change Listener ------------ { Cancelled }");
                }
            }
        });
        job.setPriority(Job.LONG);
        job.setUser(true);
        // run the job
        job.schedule();
    }

}
