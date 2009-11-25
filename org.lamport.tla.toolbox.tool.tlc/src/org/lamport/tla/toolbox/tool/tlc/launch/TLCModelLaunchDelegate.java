package org.lamport.tla.toolbox.tool.tlc.launch;

import java.io.ByteArrayInputStream;
import java.util.Hashtable;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.jobs.JobChangeAdapter;
import org.eclipse.core.runtime.jobs.MultiRule;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.LaunchConfigurationDelegate;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.tool.IParseResult;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.job.TLCJob;
import org.lamport.tla.toolbox.tool.tlc.job.TLCProcessJob;
import org.lamport.tla.toolbox.tool.tlc.model.TypedSet;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelWriter;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.TLAMarkerInformationHolder;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;

/**
 * Represents a launch delegate for TLC<br>
 * The methods in this class are called in the following order:
 * <ol>
 * <li>getLaunch()</li>
 * <li>preLaunchCheck()</li>
 * <li>buildForLaunch()</li>
 * <li>finalLaunchCheck()</li>
 * <li>launch()</li>
 * </ol>
 * Some of them run on any launch type, others only in the modelcheck mode
 * 
 * @author Simon Zambrovski
 * @version $Id$
 * Modified on 10 Sep 2009 to add No Spec TLC launch option.
 */
public class TLCModelLaunchDelegate extends LaunchConfigurationDelegate implements IModelConfigurationConstants,
        IModelConfigurationDefaults
{
    // Mutex rule for the following jobs to run after each other
    private MutexRule mutexRule = new MutexRule();

    private String specName = null;
    private String modelName = null;
    private String specRootFilename = null;

    /**
     * Configuration type
     */
    public static final String LAUNCH_CONFIGURATION_TYPE = "org.lamport.tla.toolbox.tool.tlc.modelCheck";
    /**
     * Mode for starting TLC
     */
    public static final String MODE_MODELCHECK = "modelcheck";
    /**
     * Only generate the models but do not run TLC
     */
    public static final String MODE_GENERATE = "generate";

    /**
     * 1. method called during the launch
     */
    public ILaunch getLaunch(ILaunchConfiguration configuration, String mode) throws CoreException
    {
        // delegate to the super implementation
        return super.getLaunch(configuration, mode);
    }

    /**
     * Returns whether a launch should proceed. This method is called first
     * in the launch sequence providing an opportunity for this launch delegate
     * to abort the launch.
     * 
     * <br>2. method called on launch
     * @return whether the launch should proceed
     * @see org.eclipse.debug.core.model.ILaunchConfigurationDelegate2#preLaunchCheck(org.eclipse.debug.core.ILaunchConfiguration, java.lang.String, org.eclipse.core.runtime.IProgressMonitor)
     */
    public boolean preLaunchCheck(ILaunchConfiguration config, String mode, IProgressMonitor monitor)
            throws CoreException
    {

        // check the config existence
        if (!config.exists())
        {
            return false;
        }

        try
        {
            monitor.beginTask("Reading model parameters", 1);

            // name of the specification
            specName = config.getAttribute(SPEC_NAME, EMPTY_STRING);

            // model name
            modelName = config.getAttribute(MODEL_NAME, EMPTY_STRING);

            // root file name
            specRootFilename = ToolboxHandle.getRootModule(config.getFile().getProject()).getLocation().toOSString();
            // specRootFilename = config.getAttribute(SPEC_ROOT_FILE,
            // EMPTY_STRING);

        } finally
        {
            // finish the monitor
            monitor.done();
        }

        return true;
    }

    /**
     * Instead of building, the model files are written to the disk. 
     * The directory with the same name as the model is created as the sub-directory
     * of the spec project. (if already present, the files inside will be deleted)
     * Three new files are created: MC.tla, MC.cfg, MC.out
     * All spec modules, including the root module are copied to this directory
     *  
     * <br>3. method called on launch
     * 
     * @see org.eclipse.debug.core.model.ILaunchConfigurationDelegate2#buildForLaunch(org.eclipse.debug.core.ILaunchConfiguration, java.lang.String, org.eclipse.core.runtime.IProgressMonitor)
     */
    public boolean buildForLaunch(ILaunchConfiguration config, String mode, IProgressMonitor monitor)
            throws CoreException
    {
        // generate the model here
        int STEP = 100;

        try
        {
            monitor.beginTask("Creating model", 30);
            // step 1
            monitor.subTask("Creating directories");

            // retrieve the project containing the specification
            IProject project = ResourceHelper.getProject(specName);
            if (project == null)
            {
                // project could not be found
                throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                        "Error accessing the spec project " + specName));
            }

            // retrieve the root file
            IFile specRootFile = ResourceHelper.getLinkedFile(project, specRootFilename, false);
            if (specRootFile == null)
            {
                // root module file not found
                throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                        "Error accessing the root module " + specRootFilename));
            }

            // retrieve the model folder
            IFolder modelFolder = project.getFolder(modelName);
            IPath targetFolderPath = modelFolder.getProjectRelativePath().addTrailingSeparator();

            // create the handles: MC.tla, MC.cfg and MC.out
            IFile tlaFile = project.getFile(targetFolderPath.append(ModelHelper.FILE_TLA));
            IFile cfgFile = project.getFile(targetFolderPath.append(ModelHelper.FILE_CFG));
            IFile outFile = project.getFile(targetFolderPath.append(ModelHelper.FILE_OUT));

            TLCActivator.logDebug("Writing files to: " + targetFolderPath.toOSString());

            final IFile[] files = new IFile[] { tlaFile, cfgFile, outFile };

            if (modelFolder.exists())
            {
                final IResource[] members = modelFolder.members();
                // erase everything inside
                if (members.length == 0)
                {
                    monitor.worked(STEP);
                } else
                {
                    final boolean recover = config.getAttribute(LAUNCH_RECOVER, LAUNCH_RECOVER_DEFAULT);
                    final IResource[] checkpoints = ModelHelper.getCheckpoints(config, true);

                    ISchedulingRule deleteRule = ResourceHelper.getDeleteRule(members);

                    // delete files
                    ResourcesPlugin.getWorkspace().run(new IWorkspaceRunnable() {

                        public void run(IProgressMonitor monitor) throws CoreException
                        {
                            boolean checkFiles = recover;
                            monitor.beginTask("Deleting files", members.length);
                            // delete the members of the target
                            // directory
                            for (int i = 0; i < members.length; i++)
                            {
                                if (checkFiles)
                                {
                                    if (checkpoints.length > 0 && checkpoints[0].equals(members[i]))
                                    {
                                        // we found the recovery
                                        // directory and didn't delete
                                        // it
                                        checkFiles = false;
                                        continue;
                                    }
                                } else
                                {
                                    // delete file
                                    // either non-recovery mode
                                    // or the recovery directory already
                                    // skipped
                                    try
                                    {
                                        members[i].delete(IResource.FORCE, new SubProgressMonitor(monitor, 1));
                                    } catch (CoreException e)
                                    {
                                        // catch the exception if
                                        // deletion failed, and just
                                        // ignore this fact
                                        // FIXME this should be fixed at
                                        // some later point in time
                                        TLCActivator.logError("Error deleting a file " + members[i].getLocation(), e);
                                    }
                                }
                            }
                            monitor.done();
                        }
                    }, deleteRule, IWorkspace.AVOID_UPDATE, new SubProgressMonitor(monitor, STEP));
                }
            } else
            {
                // create it
                modelFolder.create(IResource.DERIVED | IResource.FORCE, true, new SubProgressMonitor(monitor, STEP));
            }

            // step 2
            monitor.subTask("Copying files");

            // copy
            specRootFile.copy(targetFolderPath.append(specRootFile.getProjectRelativePath()), IResource.DERIVED
                    | IResource.FORCE, new SubProgressMonitor(monitor, 1));
            // find the result
            IResource specRootFileCopy = modelFolder.findMember(specRootFile.getProjectRelativePath());

            // react if no result
            if (specRootFileCopy == null)
            {
                throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID, "Error copying "
                        + specRootFilename + " into " + targetFolderPath.toOSString()));
            }

            // get the list of dependent modules
            List extendedModules = ToolboxHandle.getExtendedModules(specRootFile.getName());

            // iterate and copy modules that are needed for the spec
            IFile moduleFile = null;
            for (int i = 0; i < extendedModules.size(); i++)
            {
                String module = (String) extendedModules.get(i);
                // only take care of user modules
                if (ToolboxHandle.isUserModule(module))
                {
                    moduleFile = ResourceHelper.getLinkedFile(project, module, false);
                    if (moduleFile != null)
                    {
                        moduleFile.copy(targetFolderPath.append(moduleFile.getProjectRelativePath()), IResource.DERIVED
                                | IResource.FORCE, new SubProgressMonitor(monitor, STEP / extendedModules.size()));
                    }

                    // TODO check the existence of copied files
                }
            }

            // get the scheduling rule
            ISchedulingRule fileRule = MultiRule.combine(ResourceHelper.getModifyRule(files), ResourceHelper
                    .getCreateRule(files));

            // create files
            ResourcesPlugin.getWorkspace().run(new IWorkspaceRunnable() {
                public void run(IProgressMonitor monitor) throws CoreException
                {
                    for (int i = 0; i < files.length; i++)
                    {
                        if (files[i].exists())
                        {
                            files[i].setContents(new ByteArrayInputStream("".getBytes()), IResource.DERIVED
                                    | IResource.FORCE, new SubProgressMonitor(monitor, 1));
                        } else
                        {
                            files[i].create(new ByteArrayInputStream("".getBytes()), IResource.DERIVED
                                    | IResource.FORCE, new SubProgressMonitor(monitor, 1));
                        }
                    }
                }

            }, fileRule, IWorkspace.AVOID_UPDATE, new SubProgressMonitor(monitor, STEP));

            monitor.worked(STEP);
            monitor.subTask("Creating contents");

            ModelWriter writer = new ModelWriter();

            // add extend primer
            writer.addPrimer(ModelHelper.MC_MODEL_NAME, ResourceHelper.getModuleName(specRootFilename));

            // constants list
            List constants = ModelHelper.deserializeAssignmentList(config.getAttribute(MODEL_PARAMETER_CONSTANTS,
                    new Vector()));

            // the advanced model values
            TypedSet modelValues = TypedSet.parseSet(config.getAttribute(MODEL_PARAMETER_MODEL_VALUES, EMPTY_STRING));

            // add constants and model values
            writer.addConstants(constants, modelValues, MODEL_PARAMETER_CONSTANTS, MODEL_PARAMETER_MODEL_VALUES);

            // new definitions
            writer.addNewDefinitions(config.getAttribute(MODEL_PARAMETER_NEW_DEFINITIONS, EMPTY_STRING),
                    MODEL_PARAMETER_NEW_DEFINITIONS);

            // definition overrides list
            List overrides = ModelHelper.deserializeAssignmentList(config.getAttribute(MODEL_PARAMETER_DEFINITIONS,
                    new Vector()));
            writer.addFormulaList(ModelWriter.createOverridesContent(overrides, ModelWriter.DEFOV_SCHEME), "CONSTANT",
                    MODEL_PARAMETER_DEFINITIONS);

            // constraint
            writer.addFormulaList(ModelWriter.createSourceContent(MODEL_PARAMETER_CONSTRAINT,
                    ModelWriter.CONSTRAINT_SCHEME, config), "CONSTRAINT", MODEL_PARAMETER_CONSTRAINT);
            // action constraint
            writer.addFormulaList(ModelWriter.createSourceContent(MODEL_PARAMETER_ACTION_CONSTRAINT,
                    ModelWriter.ACTIONCONSTRAINT_SCHEME, config), "ACTION_CONSTRAINT",
                    MODEL_PARAMETER_ACTION_CONSTRAINT);
            // Changed from incorrect "ACTION-CONSTRAINT" on 11 Sep 2009
            // view
            writer.addView(config.getAttribute(LAUNCH_VIEW, EMPTY_STRING), MODEL_PARAMETER_VIEW);
            // calculator expression
            writer.addConstantExpressionEvaluation(config.getAttribute(MODEL_EXPRESSION_EVAL, EMPTY_STRING), MODEL_EXPRESSION_EVAL);

            int specType = config.getAttribute(MODEL_BEHAVIOR_SPEC_TYPE, MODEL_BEHAVIOR_TYPE_DEFAULT);
            switch (specType) {
            case MODEL_BEHAVIOR_TYPE_NO_SPEC:
                ModuleNode rootModuleNode = ModelHelper.getRootModuleNode();
                if (rootModuleNode != null)
                {
                    OpDeclNode[] vars = rootModuleNode.getVariableDecls();
                    if (vars != null && vars.length > 0)
                    {
                        String var = rootModuleNode.getVariableDecls()[0].getName().toString();
                        writer.addFormulaList(ModelWriter.createFalseInit(var), "INIT", MODEL_BEHAVIOR_NO_SPEC);
                        writer.addFormulaList(ModelWriter.createFalseNext(var), "NEXT", MODEL_BEHAVIOR_NO_SPEC);
                    }
                }  
                break;
            case MODEL_BEHAVIOR_TYPE_SPEC_CLOSED:

                // the specification name-formula pair
                writer.addFormulaList(ModelWriter.createSourceContent(MODEL_BEHAVIOR_CLOSED_SPECIFICATION,
                        ModelWriter.SPEC_SCHEME, config), "SPECIFICATION", MODEL_BEHAVIOR_CLOSED_SPECIFICATION);
                break;
            case MODEL_BEHAVIOR_TYPE_SPEC_INIT_NEXT:

                // the init and next formulas
                writer.addFormulaList(ModelWriter.createSourceContent(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT,
                        ModelWriter.INIT_SCHEME, config), "INIT", MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT);
                writer.addFormulaList(ModelWriter.createSourceContent(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT,
                        ModelWriter.NEXT_SCHEME, config), "NEXT", MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT);
                break;
            }

            // // the specification name-formula pair
            // writer.addSpecDefinition(ModelHelper.createSpecificationContent(config),
            // MODEL_BEHAVIOR_CLOSED_SPECIFICATION);

            // invariants
            writer.addFormulaList(ModelWriter.createFormulaListContent(config.getAttribute(
                    MODEL_CORRECTNESS_INVARIANTS, new Vector()), ModelWriter.INVARIANT_SCHEME), "INVARIANT",
                    MODEL_CORRECTNESS_INVARIANTS);

            // properties
            writer.addFormulaList(ModelWriter.createFormulaListContent(config.getAttribute(
                    MODEL_CORRECTNESS_PROPERTIES, new Vector()), ModelWriter.PROP_SCHEME), "PROPERTY",
                    MODEL_CORRECTNESS_PROPERTIES);

            monitor.worked(STEP);
            monitor.subTask("Writing contents");

            // write down the files
            writer.writeFiles(tlaFile, cfgFile, monitor);

            // refresh the model folder
            modelFolder.refreshLocal(IResource.DEPTH_ONE, new SubProgressMonitor(monitor, STEP));

        } finally
        {
            // make sure to complete the monitor
            monitor.done();
        }

        // we don't want to rebuild the workspace
        return false;
    }

    /**
     * Launch the module parser on the root module and handle the errors
     *   
     * 
     * <br>4. method called on launch
     * @see org.eclipse.debug.core.model.ILaunchConfigurationDelegate2#finalLaunchCheck(org.eclipse.debug.core.ILaunchConfiguration, java.lang.String, org.eclipse.core.runtime.IProgressMonitor)
     */
    public boolean finalLaunchCheck(ILaunchConfiguration configuration, String mode, IProgressMonitor monitor)
            throws CoreException
    {
        monitor.beginTask("Verifying model files", 4);

        IProject project = ResourceHelper.getProject(specName);
        IFolder launchDir = project.getFolder(modelName);
        IFile rootModule = launchDir.getFile(ModelHelper.FILE_TLA);

        monitor.worked(1);
        // parse the MC file
        IParseResult parseResult = ToolboxHandle.parseModule(rootModule, new SubProgressMonitor(monitor, 1), false,
                false);
        Vector detectedErrors = parseResult.getDetectedErrors();
        boolean status = !AdapterFactory.isProblemStatus(parseResult.getStatus());

        monitor.worked(1);
        // remove existing markers
        ModelHelper.removeModelProblemMarkers(configuration, ModelHelper.TLC_MODEL_ERROR_MARKER_SANY);
        monitor.worked(1);

        if (!detectedErrors.isEmpty())
        {
            TLCActivator.logDebug("Errors in model file found " + rootModule.getLocation());
        }

        try
        {
            FileEditorInput fileEditorInput = new FileEditorInput((IFile) rootModule);
            FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();
            fileDocumentProvider.connect(fileEditorInput);

            // The document for manipulation of the MC.tla file
            IDocument document = fileDocumentProvider.getDocument(fileEditorInput);

            // the find/replace adapter to find texts in the document
            FindReplaceDocumentAdapter searchAdapter = new FindReplaceDocumentAdapter(document);

            for (int i = 0; i < detectedErrors.size(); i++)
            {
                // the holder has the information about the error in the MC file
                TLAMarkerInformationHolder markerHolder = (TLAMarkerInformationHolder) detectedErrors.get(i);
                String message = markerHolder.getMessage();
                if (markerHolder.getModuleName() != null)
                {
                    // the root module is MC.tla
                    if (markerHolder.getModuleName().equals(rootModule.getName()))
                    {
                        int severity = markerHolder.getSeverityError();
                        int[] coordinates = markerHolder.getCoordinates();

                        // find the error cause and install the error marker on the corresponding
                        // field
                        Hashtable props = ModelHelper.createMarkerDescription(configuration, document, searchAdapter,
                                message, severity, coordinates);
                        if (props != null)
                        {
                            ModelHelper.installModelProblemMarker(configuration.getFile(), props,
                                    ModelHelper.TLC_MODEL_ERROR_MARKER_SANY);
                        }

                    } else
                    {
                        // the reported error is not pointing to the MC file.
                        throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                                "Fatal error during validation of the model. "
                                        + "SANY discovered an error somewhere else than the MC file. "
                                        + "This is a bug. The error message was " + message + " in the module "
                                        + markerHolder.getModuleName()));
                    }
                } else
                {
                    throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                            "Fatal error during validation of the model. "
                                    + "SANY discovered an error somewhere else than the MC file. "
                                    + "This is a bug. The error message was " + message + "."));
                }

            }

        } finally
        {
            monitor.done();
        }

        if (MODE_GENERATE.equals(mode))
        {
            // generation is done
            // nothing to do more
            return false;
        } else
        {
            TLCActivator.logDebug("Final check for the " + mode + " mode. The result of the check is " + status);
            return status;
        }
    }

    /**
     * 5. method called on launch
     * Main launch method called by the platform on model launches
     */
    public void launch(ILaunchConfiguration config, String mode, ILaunch launch, IProgressMonitor monitor)
            throws CoreException
    {

        // check the modes
        if (!MODE_MODELCHECK.equals(mode))
        {
            throw new CoreException(
                    new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID, "Unsupported launch mode " + mode));
        }

        // retrieve the project containing the specification
        IProject project = ResourceHelper.getProject(specName);
        if (project == null)
        {
            // project could not be found
            throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                    "Error accessing the spec project " + specName));
        }

        // check and lock the model
        synchronized (config)
        {
            // read out the running attribute
            if (ModelHelper.isModelLocked(config))
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
                // from this point any termination of the run must reset the
                // flag
                ModelHelper.lockModel(config);
            }
        }

        // number of workers
        int numberOfWorkers = config.getAttribute(LAUNCH_NUMBER_OF_WORKERS, LAUNCH_NUMBER_OF_WORKERS_DEFAULT);

        // TLC job
        // TLCJob tlcjob = new TLCInternalJob(tlaFile, cfgFile, project);
        TLCJob tlcjob = new TLCProcessJob(specName, modelName, launch);
        tlcjob.setWorkers(numberOfWorkers);
        tlcjob.setPriority(Job.LONG);
        tlcjob.setUser(true);
        // The TLC job itself does not do any file IO
        tlcjob.setRule(mutexRule);

        // setup the job change listener
        TLCJobChangeListener tlcJobListener = new TLCJobChangeListener(config);
        tlcjob.addJobChangeListener(tlcJobListener);
        tlcjob.schedule();
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
                TLCActivator.logError("Error unlocking the model", e);
            }
        }
    }

    /**
     * A listener writing the job state to the System.out
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

    /**
     * A simple mutex rule 
     */
    class MutexRule implements ISchedulingRule
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
}
