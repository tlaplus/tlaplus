package org.lamport.tla.toolbox.tool.tlc.launch;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
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
    public static final String LAUNCH_CONFIGURATION_TYPE = "org.lamport.tla.toolbox.tool.tlc.modelCheck";
    public static final String MODE_MODELCHECK = "modelcheck";

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
        if (!config.exists()) 
        {
            throw new CoreException(
                    new Status(
                            IStatus.ERROR,
                            TLCActivator.PLUGIN_ID,
                            "Tried to start a model that does not exist."));
        }

        
        // name of the specification
        String specName = config.getAttribute(SPEC_NAME, EMPTY_STRING);

        // model name
        String modelName = config.getAttribute(MODEL_NAME, EMPTY_STRING);

        // read out the running attribute
        boolean isRunning = ModelHelper.isModelLocked(config);

        // retrieve the project containing the specification
        IProject project = ResourceHelper.getProject(specName);
        if (project == null)
        {
            // project could not be found
            throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                    "Error accessing the spec project " + specName));
        }

        if (isRunning)
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
        } else
        {

            // setup the running flag
            // from this point any termination of the run must reset the flag
            ModelHelper.lockModel(config);
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
        ISchedulingRule modelRule = MultiRule.combine(mutexRule, ResourceHelper.getModifyRule(project));
        modelJob.setRule(modelRule);

        // TLC job
        // TLCJob tlcjob = new TLCInternalJob(tlaFile, cfgFile, project);
        TLCJob tlcjob = new TLCProcessJob(specName, modelName, launch);
        tlcjob.setWorkers(numberOfWorkers);
        tlcjob.setPriority(Job.LONG);
        tlcjob.setUser(true);
        // The TLC job itself does not do any file IO
        tlcjob.setRule(mutexRule);

        // setup the job listener. which reacts on termination and errors
        ModelJobChangeListener modelJobListener = new ModelJobChangeListener(config, tlcjob);
        modelJob.addJobChangeListener(modelJobListener);

        // setup the job change listener
        TLCJobChangeListener tlcJobListener = new TLCJobChangeListener(config);
        tlcjob.addJobChangeListener(tlcJobListener);

        // launch the jobs
        modelJob.schedule();
        tlcjob.schedule();
    }

    /**
     * listens to the termination of the model creation job 
     */
    class ModelJobChangeListener extends SimpleJobChangeListener
    {
        private ILaunchConfiguration config;
        private Job tlcJob;

        /**
         * Constructs the change listener
         * @param config the config to modify after the job completion
         * @param cancelJob a job to cancel on abnormal termination of the current one
         */
        public ModelJobChangeListener(ILaunchConfiguration config, Job cancelJob)
        {
            this.config = config;
            this.tlcJob = cancelJob;
        }

        public void done(IJobChangeEvent event)
        {
            super.done(event);
            if (!event.getResult().isOK())
            {
                // job is canceled by the user or terminated with an error
                // at any rate, make sure to cancel the TLC job
                this.tlcJob.cancel();

                // make the model modification in order to make it runnable again
                try
                {
                    ModelHelper.unlockModel(config);
                } catch (CoreException e)
                {
                    e.printStackTrace();
                }
            }
        }
    }

    /**
     * listens to the termination of the TLC run 
     */
    class TLCJobChangeListener extends SimpleJobChangeListener
    {
        private ILaunchConfiguration config;

        /**
         * Constructs the change listener
         * @param config the config to modify after the job completion
         */
        public TLCJobChangeListener(ILaunchConfiguration config)
        {
            this.config = config;
        }

        public void done(IJobChangeEvent event)
        {
            super.done(event);
            // make the model modification in order to make it runnable again
            try
            {
                ModelHelper.unlockModel(config);
            } catch (CoreException e)
            {
                e.printStackTrace();
            }
        }
    }

    /**
     * A listener writing the  
     */
    class SimpleJobChangeListener extends JobChangeAdapter
    {

        public void done(IJobChangeEvent event)
        {
            String jobName = event.getJob().getName();
            String status = null;
            if (event.getResult().isOK())
            {
                status = "Done";
            } else
            {
                // analyze the cause
                switch (event.getResult().getSeverity()) {
                case IStatus.CANCEL:
                    status = "Cancelled";
                    break;
                case IStatus.ERROR:
                    status = "Error";
                    break;
                default:
                    status = "Unknown";
                    break;
                }
            }
            System.out.println("Job '" + jobName + "' terminated with status: { " + status + " }");
        }
    };

}
