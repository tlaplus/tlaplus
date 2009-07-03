package org.lamport.tla.toolbox.tool.tlc.launch;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.IJobChangeListener;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.jobs.JobChangeAdapter;
import org.eclipse.core.runtime.jobs.MultiRule;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.ILaunchConfigurationDelegate;
import org.eclipse.debug.core.model.LaunchConfigurationDelegate;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.job.ModelCreationJob;
import org.lamport.tla.toolbox.tool.tlc.job.TLCJob;
import org.lamport.tla.toolbox.tool.tlc.job.TLCProcessJob;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
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

    /**
     * A simple mutex rule 
     */
    public class MutexRule implements ISchedulingRule
    {
        public boolean isConflicting(ISchedulingRule rule)
        {
            return rule == this;
        }
        public boolean contains(ISchedulingRule rule)
        {
            return rule == this;
        }
    }

    public void launch(ILaunchConfiguration config, String mode, ILaunch launch, IProgressMonitor monitor)
            throws CoreException
    {
        // name of the specification
        String specName = config.getAttribute(SPEC_NAME, EMPTY_STRING);

        // model name
        String modelName = config.getAttribute(MODEL_NAME, EMPTY_STRING);

        // retrieve the project containing the specification
        IProject project = ResourceHelper.getProject(specName);
        if (project == null)
        {
            // project could not be found
            throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                    "Error accessing the spec project " + specName));
        }

        if (ModelHelper.hasLock(modelName, project))
        {
            // previous run has not been completed
            // exit
            throw new CoreException(
                    new Status(
                            IStatus.ERROR,
                            TLCActivator.PLUGIN_ID,
                            "The lock for "
                                    + modelName
                                    + " has been found. Another TLC is possible running on the same model, or has been terminated non-gracefully"));
        }

        // Mutex rule for the following jobs to run after each other 
        MutexRule mutexRule = new MutexRule();

        // number of workers
        int numberOfWorkers = config.getAttribute(LAUNCH_NUMBER_OF_WORKERS, LAUNCH_NUMBER_OF_WORKERS_DEFAULT);

        // model job
        ModelCreationJob modelJob = new ModelCreationJob(specName, modelName, config);
        modelJob.setPriority(Job.SHORT);
        // the combination of two rules is used
        // the mutexRule prevents TLCProcessJob from running during the files are being written
        // the modify rule prevents modifications of the project during the creation of the model files
        ISchedulingRule combinedRule1 = MultiRule.combine(mutexRule, ResourceHelper.getModifyRule(project));
        modelJob.setRule(combinedRule1);
        modelJob.schedule();

        // TLC job
        // TLCJob tlcjob = new TLCInternalJob(tlaFile, cfgFile, project);
        TLCJob tlcjob = new TLCProcessJob(specName, modelName, launch);
        tlcjob.setWorkers(numberOfWorkers);
        tlcjob.addJobChangeListener(writingJobStatusListener);
        tlcjob.setPriority(Job.LONG);
        tlcjob.setUser(true);
        tlcjob.setRule(mutexRule);
        tlcjob.schedule();
    }

}
