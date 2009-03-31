package org.lamport.tla.toolbox.tool.tlc.launch;

import org.eclipse.core.resources.IFile;
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
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

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
        // String rootModuleFile = config.getAttribute(SPEC_ROOT_FILE, EMPTY_STRING);
        String rootModuleName = config.getAttribute(SPEC_ROOT_MODULE, EMPTY_STRING);

        System.out.println("Staring TLC on model " + modelName + " of spec " + specName + " in mode " + mode);

        
        String tlaFilename = config.getAttribute(MODEL_ROOT_FILE, EMPTY_STRING);
        String configFilename = config.getAttribute(CONFIG_FILE, EMPTY_STRING);
        
        System.out.println("Model TLA file is: " + tlaFilename);
        System.out.println("Model CFG file is: " + configFilename);
        
        
        // root file
        IFile rootModule = (IFile) ToolboxHandle.getCurrentSpec().getProject().findMember(new Path(tlaFilename).lastSegment());
        
        // config file
        IFile cfgFile = (IFile) ToolboxHandle.getCurrentSpec().getProject().findMember(new Path(configFilename).lastSegment());

        
        ModelWriter writer = new ModelWriter();
        // add extend primer
        writer.addPrimer(tlaFilename, rootModuleName);
        
        // the specification name-formula pair
        writer.addSpecDefinition(ModelHelper.createSpecificationContent(config));

        // write the content
        writer.writeFiles(rootModule, cfgFile, monitor);
        
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
