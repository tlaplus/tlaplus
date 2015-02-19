package org.lamport.tla.toolbox.tool.tlc.launch;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.net.URL;
import java.util.Hashtable;
import java.util.List;
import java.util.Properties;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.resources.WorkspaceJob;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtensionRegistry;
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
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.tool.IParseResult;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.job.DistributedTLCJob;
import org.lamport.tla.toolbox.tool.tlc.job.ITLCJobStatus;
import org.lamport.tla.toolbox.tool.tlc.job.TLCJobFactory;
import org.lamport.tla.toolbox.tool.tlc.job.TLCProcessJob;
import org.lamport.tla.toolbox.tool.tlc.model.TypedSet;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelWriter;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.TLAMarkerInformationHolder;
import org.osgi.framework.BundleContext;
import org.osgi.framework.FrameworkUtil;
import org.osgi.framework.ServiceReference;

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
    protected MutexRule mutexRule = new MutexRule();

    protected String specName = null;
    protected String modelName = null;
    protected String specRootFilename = null;

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

            TLCActivator.getDefault().logDebug("Writing files to: " + targetFolderPath.toOSString());

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
                    final IResource[] checkpoints = ModelHelper.getCheckpoints(config, false);

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
                                        if (!members[i].getName().equals(ModelHelper.TE_TRACE_SOURCE))
                                        {
                                            members[i].delete(IResource.FORCE, new SubProgressMonitor(monitor, 1));
                                        }
                                    } catch (CoreException e)
                                    {
                                        // catch the exception if
                                        // deletion failed, and just
                                        // ignore this fact
                                        // FIXME this should be fixed at
                                        // some later point in time
                                        TLCActivator.getDefault().logError("Error deleting a file " + members[i].getLocation(), e);
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
       
            // add the MODULE beginning and EXTENDS statement
            writer.addPrimer(ModelHelper.MC_MODEL_NAME, ResourceHelper.getModuleName(specRootFilename));

            // Sets constants to a Vector of the substitutions for the CONSTANT substitutions
            List constants = ModelHelper.deserializeAssignmentList(config.getAttribute(MODEL_PARAMETER_CONSTANTS,
                    new Vector()));

            // Sets modelValues to a TypedSet object whose value is a String array containing
            // the names of the model values declared on the Advanced model page.
            TypedSet modelValues = TypedSet.parseSet(config.getAttribute(MODEL_PARAMETER_MODEL_VALUES, EMPTY_STRING));

            // Adds to MC.cfg the CONSTANT declarations for (in order) 
            //  - The model values declared on the advanced model page.
            //  - Each CONSTANT parameter instantiated with a model value or set of model values.
            //  - SYMMETRY declarations.
            // Adds to MC.tla the CONSTANT declarations for (in order)
            //  - The model values declared on the advanced model page.
            //  - The model values introduced when instantiating a CONSTANT parameter with a set of model values.
            //  - The definitions of each CONSTANT parameter declared as a set of model values in the MC.cfg file.
            //  - Definitions of symmetry sets for the CONSTANT parameters.
            writer.addConstants(constants, modelValues, MODEL_PARAMETER_CONSTANTS, MODEL_PARAMETER_MODEL_VALUES);
            
            // The additional definitions from the Advanced model page.
            writer.addNewDefinitions(config.getAttribute(MODEL_PARAMETER_NEW_DEFINITIONS, EMPTY_STRING),
                    MODEL_PARAMETER_NEW_DEFINITIONS);

            // Adds to MC.cfg the CONSTANT declarations for CONSTANT parameters instantiated with ordinary values. 
            // Adds to MC.tla the definitions for the new symbols introduced for the aforementioned CONSTANT parameters.
            writer.addConstantsBis(constants, MODEL_PARAMETER_CONSTANTS);

            // Sets overrides to the Vector of definition overrides.
            List overrides = ModelHelper.deserializeAssignmentList(config.getAttribute(MODEL_PARAMETER_DEFINITIONS,
                    new Vector()));
            
            // For the definition overrides, it adds the definitions to the MC.tla file and the
            // overriding CONSTANT statements to the MC.cfg file.
            writer.addFormulaList(ModelWriter.createOverridesContent(overrides, ModelWriter.DEFOV_SCHEME), "CONSTANT",
                    MODEL_PARAMETER_DEFINITIONS);

            /* 
             * specType is used to write the desired spec or lack of spec to the MC files.
             * 
             * specType is also used to make sure that aspects of the model that are not relevant
             * when there is no behavior spec are not written. In particular, the following should
             * be ignored when there is no behavior spec:
             * 
             * 1.) Invariants
             * 2.) Properties
             * 3.) State constraint
             * 4.) Action constraint
             * 5.) View
             * 
             * Recover from checkpoint and TLC options should also be ignored, but
             * that is done in TLCJob.constructProgramArguments().
             */
            int specType = config.getAttribute(MODEL_BEHAVIOR_SPEC_TYPE, MODEL_BEHAVIOR_TYPE_DEFAULT);
            boolean hasSpec = specType != MODEL_BEHAVIOR_TYPE_NO_SPEC;

            if (hasSpec)
            {
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
            }

            // calculator expression
            writer.addConstantExpressionEvaluation(config.getAttribute(MODEL_EXPRESSION_EVAL, EMPTY_STRING),
                    MODEL_EXPRESSION_EVAL);

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

            // do not write invariants and properties if there is no behavior spec
            if (hasSpec)
            {
                // invariants
                writer.addFormulaList(ModelWriter.createFormulaListContent(config.getAttribute(
                        MODEL_CORRECTNESS_INVARIANTS, new Vector()), ModelWriter.INVARIANT_SCHEME), "INVARIANT",
                        MODEL_CORRECTNESS_INVARIANTS);

                // properties
                writer.addFormulaList(ModelWriter.createFormulaListContent(config.getAttribute(
                        MODEL_CORRECTNESS_PROPERTIES, new Vector()), ModelWriter.PROP_SCHEME), "PROPERTY",
                        MODEL_CORRECTNESS_PROPERTIES);
            }

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
            TLCActivator.getDefault().logDebug("Errors in model file found " + rootModule.getLocation());
        }

        FileEditorInput fileEditorInput = new FileEditorInput((IFile) rootModule);
        FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();
        try
        {

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
            /*
             * The document provider is not needed. Always disconnect it to avoid a memory leak.
             * 
             * Keeping it connected only seems to provide synchronization of
             * the document with file changes. That is not necessary in this context.
             */
            fileDocumentProvider.disconnect(fileEditorInput);
            monitor.done();
        }

        if (MODE_GENERATE.equals(mode))
        {
            // generation is done
            // nothing to do more
            return false;
        } else
        {
            TLCActivator.getDefault().logDebug("Final check for the " + mode + " mode. The result of the check is " + status);
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
            if (ModelHelper.isModelRunning(config) || ModelHelper.isModelLocked(config))
            {
                // previous run has not been completed
                // exit
                throw new CoreException(
                        new Status(
                                IStatus.ERROR,
                                TLCActivator.PLUGIN_ID,
                                "The running attribute for "
                                        + modelName
                                        + " has been set to true or that model is locked."
                                        + "Another TLC is possible running on the same model, or has been terminated non-gracefully"
                                        + "or the user has tried to run TLC on a locked model. Running TLC on a locked model should not be possible."));
            } else
            {

                // setup the running flag
                // from this point any termination of the run must reset the
                // flag
                ModelHelper.setModelRunning(config, true);
            }
        }

        // set the model to have the original trace shown
        ModelHelper.setOriginalTraceShown(config, true);

        // number of workers
        int numberOfWorkers = config.getAttribute(LAUNCH_NUMBER_OF_WORKERS, LAUNCH_NUMBER_OF_WORKERS_DEFAULT);

        // distributed launch (legacy launch configurations pre-dating TLC distributed functionality 
        // do not have the LAUNCH_DISTRIBUTED attribute. Then, it obviously defaults to distribution turned off.
        // Trying to lookup a non-existing attribute would cause a runtime exception.)
        // Then it could also be true or false. The legacy flag showing if "ad hoc" distribution is turned
        // on or not. Simply map it to "ad hoc" or "off".
        String cloud = "off";
        if (config.hasAttribute(LAUNCH_DISTRIBUTED)) {
        	try {
        		cloud = config.getAttribute(LAUNCH_DISTRIBUTED, LAUNCH_DISTRIBUTED_DEFAULT);
        	} catch (CoreException e) {
        		boolean distributed = config.getAttribute(LAUNCH_DISTRIBUTED, false);
        		if (distributed) {
        			cloud = "ad hoc";
        		}
        	}
        }
        
        // TLC job
        Job job = null;
        if("off".equalsIgnoreCase(cloud)) {
        	job = new TLCProcessJob(specName, modelName, launch, numberOfWorkers);
            // The TLC job itself does not do any file IO
            job.setRule(mutexRule);
        } else {
        	if ("ad hoc".equalsIgnoreCase(cloud)) {
        		job = new DistributedTLCJob(specName, modelName, launch, numberOfWorkers);
                job.setRule(mutexRule);
        	} else {
                //final IProject iproject = ResourceHelper.getProject(specName);
                final IFolder launchDir = project.getFolder(modelName);
                final File file = launchDir.getRawLocation().makeAbsolute().toFile();

				final BundleContext bundleContext = FrameworkUtil.getBundle(
						TLCModelLaunchDelegate.class).getBundleContext();
				final ServiceReference<IExtensionRegistry> serviceReference = bundleContext
						.getServiceReference(IExtensionRegistry.class);
				final IExtensionRegistry registry = bundleContext
						.getService(serviceReference);
				final IConfigurationElement[] elements = registry
						.getConfigurationElementsFor("org.lamport.tla.toolx.tlc.job");
				for (IConfigurationElement element : elements) {
					final TLCJobFactory factory = (TLCJobFactory) element
							.createExecutableExtension("clazz");
					final Properties props = new Properties();
					props.put(TLCJobFactory.MAIN_CLASS, tlc2.TLC.class.getName());
					props.put(TLCJobFactory.MAIL_ADDRESS, config.getAttribute(
							LAUNCH_DISTRIBUTED_RESULT_MAIL_ADDRESS, "tlc@localhost"));
					job = factory.getTLCJob(cloud, file, numberOfWorkers, props);
					job.addJobChangeListener(new WithStatusJobChangeListener(config));
					break;
				}
        	}
        }
        job.setPriority(Job.LONG);
        job.setUser(true);

        // setup the job change listener
        TLCJobChangeListener tlcJobListener = new TLCJobChangeListener(config);
        job.addJobChangeListener(tlcJobListener);
        job.schedule();
    }

	// This opens up a dialog at the end of the job showing the status message
    class WithStatusJobChangeListener extends SimpleJobChangeListener {

		private final ILaunchConfiguration config;

		public WithStatusJobChangeListener(ILaunchConfiguration config) {
			this.config = config;
		}

		public void done(IJobChangeEvent event) {
			super.done(event);
	
			// TLC models seem to require some clean-up
			try {
				ModelHelper.setModelLocked(config, false);
				ModelHelper.setModelRunning(config, false);
				ModelHelper.recoverModel(config);
			} catch (CoreException doesNotHappen) {
				doesNotHappen.printStackTrace();
				// Not supposed to happen
			}

			final IStatus status = event.getJob().getResult();
			final String message = status.getMessage();
			if (status instanceof ITLCJobStatus) {
				final ITLCJobStatus result = (ITLCJobStatus) status;
				final URL url = result.getURL();
				Display.getDefault().asyncExec(new Runnable() {
					public void run() {
						boolean yesOpenBrowser = MessageDialog
								.openConfirm(
										Display.getDefault().getActiveShell(),
										"Cloud TLC",
										message
												+ "\n\nClick OK to open a status page in your browser. "
												+ "Click Cancel to ignore the status page (you can still go there later).");
						if (yesOpenBrowser) {
							try {
								PlatformUI.getWorkbench().getBrowserSupport()
								.getExternalBrowser().openURL(url);
							} catch (PartInitException doesNotHappen) {
								doesNotHappen.printStackTrace();
							}
						}
					}
				});
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

            try
            {
                /*
                 * After the job has completed, new check points
                 * may have been created in the file system but
                 * not yet recognized by the eclipse resource
                 * framework. The following method
                 * is called with the flag to refresh. This synch's
                 * the resource framework with the new checkpoints (if any).
                 * 
                 * This refresh operation is wrapped in a job. The following
                 * explains why. To read about jobs in general, check out:
                 * http://www.eclipse.org/articles/Article-Concurrency/jobs-api.html.
                 * 
                 * The refresh operation is a long running job. This means
                 * that it cannot be run within the running code of another
                 * job whose scheduling rule does not encompass the scheduling rule
                 * of the refresh operation. This method (done()) seems to be
                 * called during the running of the TLC job. Therefore, simply
                 * calling ModelHelper.getCheckpoints(config, true) results
                 * in an exception because getCheckpoints calls the refresh
                 * operation which has a scheduling rule that is not included
                 * by the TLC job scheduling rule.
                 * 
                 * To solve this problem, we wrap the call to getCheckpoints()
                 * in another job, set the scheduling rule to be a scheduling rule
                 * for refreshing the model folder, and schedule that wrapping job
                 * to be run later.
                 */
                IProject project = ResourceHelper.getProject(specName);
                IFolder modelFolder = project.getFolder(modelName);
                WorkspaceJob refreshJob = new WorkspaceJob("") {

                    public IStatus runInWorkspace(IProgressMonitor monitor) throws CoreException
                    {
                        ModelHelper.getCheckpoints(config, true);
                        return Status.OK_STATUS;
                    }
                };
                refreshJob.setRule(ResourcesPlugin.getWorkspace().getRuleFactory().refreshRule(modelFolder));
                refreshJob.schedule();

                // make the model modification in order to make it runnable again
                if (event.getJob() instanceof TLCProcessJob) {
                	Assert.isTrue(event.getJob() instanceof TLCProcessJob);
                	Assert.isNotNull(event.getResult());
                	TLCProcessJob tlcJob = (TLCProcessJob) event.getJob();
                	if (event.getResult().isOK())
                	{
                		int autoLockTime = config.getAttribute(LAUNCH_AUTO_LOCK_MODEL_TIME,
                				IModelConfigurationDefaults.MODEL_AUTO_LOCK_TIME_DEFAULT);
                		// auto lock time is in minutes, getTLCStartTime() and getTLCEndTime()
                		// are in milliseconds
                		if (tlcJob.getTlcEndTime() - tlcJob.getTlcStartTime() > autoLockTime * 60 * 1000)
                		{
                			// length of job execution exceeded a certain length of time
                			// should lock
                			ModelHelper.setModelLocked(config, true);
                		}
                	}
                }

                ModelHelper.setModelRunning(config, false);
            } catch (CoreException e)
            {
                TLCActivator.getDefault().logError("Error setting lock and running markers on the model", e);
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
            TLCActivator.getDefault().logDebug("Job '" + jobName + "' terminated with status: { " + status + " }");
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
