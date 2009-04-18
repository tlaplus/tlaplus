package org.lamport.tla.toolbox.tool.tlc.launch;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.IJobChangeListener;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.jobs.JobChangeAdapter;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.ILaunchConfigurationDelegate;
import org.eclipse.debug.core.model.LaunchConfigurationDelegate;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.job.ModelCreationJob;
import org.lamport.tla.toolbox.tool.tlc.job.TLCJob;
import org.lamport.tla.toolbox.util.ResourceHelper;

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
    private IJobChangeListener writingJobStatusListener = new JobChangeAdapter() {

        public void done(IJobChangeEvent event)
        {
            String jobName = event.getJob().getName();
            String status = null;
            if (event.getResult().isOK())
            {
                status = "Done";
            } else
            {
                status = "Cancelled";
            }
            System.out.println("JOB Change Listener: " + jobName + " -> { " + status + " }");
        }
    };

    public void launch(ILaunchConfiguration config, String mode, ILaunch launch, IProgressMonitor monitor)
            throws CoreException
    {

        // name of the specification
        String specName = config.getAttribute(SPEC_NAME, EMPTY_STRING);
        // model name
        String modelName = config.getAttribute(MODEL_NAME, EMPTY_STRING);
        // TLA model file
        String tlaFilename = config.getAttribute(MODEL_ROOT_FILE, EMPTY_STRING);
        // CFG file 
        String configFilename = config.getAttribute(CONFIG_FILE, EMPTY_STRING);
        // number of workers
        int numberOfWorkers = config.getAttribute(LAUNCH_NUMBER_OF_WORKERS, LAUNCH_NUMBER_OF_WORKERS_DEFAULT);

        System.out.println("Staring TLC on model " + modelName + " of spec " + specName + " in mode " + mode);
        
        
        // project directory
        IProject projectDir = ToolboxHandle.getCurrentSpec().getProject();
        // model TLA file
        IFile tlaFile = (IFile) projectDir.findMember(new Path(tlaFilename).lastSegment());
        // config file
        IFile cfgFile = (IFile) projectDir.findMember(new Path(configFilename).lastSegment());

        // model job
        ModelCreationJob modelJob = new ModelCreationJob(config, tlaFile, cfgFile);
        modelJob.setPriority(Job.SHORT);
        modelJob.setRule(ResourceHelper.getModifyRule(new IResource[] { cfgFile, tlaFile }));
        // run the job
        modelJob.schedule();

        // TLC job
        TLCJob tlcjob = new TLCJob(tlaFile, cfgFile, projectDir);
        tlcjob.setWorkers(numberOfWorkers);
        tlcjob.addJobChangeListener(writingJobStatusListener);
        tlcjob.setPriority(Job.LONG);
        tlcjob.setUser(true);
        tlcjob.setRule(ResourceHelper.getModifyRule(new IResource[] { cfgFile, tlaFile }));
        
        // run the job
        tlcjob.schedule();
    }

}
