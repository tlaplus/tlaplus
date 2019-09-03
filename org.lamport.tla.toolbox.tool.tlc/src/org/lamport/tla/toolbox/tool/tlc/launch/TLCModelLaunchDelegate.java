package org.lamport.tla.toolbox.tool.tlc.launch;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Random;
import java.util.Vector;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.stream.Collectors;

import org.eclipse.core.internal.resources.ResourceException;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.resources.WorkspaceJob;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.jobs.JobChangeAdapter;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.Launch;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.debug.core.model.IStreamsProxy;
import org.eclipse.debug.core.model.LaunchConfigurationDelegate;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
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
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.model.ModelWriter;
import org.lamport.tla.toolbox.tool.tlc.model.TLCSpec;
import org.lamport.tla.toolbox.tool.tlc.model.TypedSet;
import org.lamport.tla.toolbox.tool.tlc.output.IProcessOutputSink;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.TLAMarkerInformationHolder;
import org.osgi.framework.BundleContext;
import org.osgi.framework.FrameworkUtil;
import org.osgi.framework.ServiceReference;

import pcal.Validator;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tlc2.TLCGlobals;
import tlc2.util.FP64;
import util.ExecutionStatisticsCollector;

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
 * Modified on 10 Sep 2009 to add No Spec TLC launch option.
 */
@SuppressWarnings("restriction")
public class TLCModelLaunchDelegate extends LaunchConfigurationDelegate
		implements IModelConfigurationConstants, IModelConfigurationDefaults {
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
    
    private static final AtomicBoolean PERFORM_VALIDATION_BEFORE_LAUNCH = new AtomicBoolean(true);


    // Mutex rule for the following jobs to run after each other
    protected MutexRule mutexRule = new MutexRule();

    private Launch launch;

    /**
     * 1. method called during the launch
     */
    public ILaunch getLaunch(ILaunchConfiguration configuration, String mode) throws CoreException
    {
		// MAK 02/22/2018 changed super.getLaunch(...) - which returned null - to
		// explicitly create the Launch instance here to get hold of the instance.
		// Return null here causes
		// org.eclipse.debug.internal.core.LaunchConfiguration.launch(String,
		// IProgressMonitor, boolean, boolean) to create the instance but it doesn't
		// correctly clean up the instance if our finalLaunchCheck below throws an
		// error. This in turn causes calls to
		// org.lamport.tla.toolbox.tool.tlc.model.Model.isRunning() to return true even
		// though finalLaunchCheck threw an exception.
    	this.launch = new Launch(configuration, mode, null);
		return launch;
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
	public boolean preLaunchCheck(final ILaunchConfiguration config, final String mode, final IProgressMonitor monitor)
			throws CoreException {
        // check the config existence
		if (!config.exists()) {
            return false;
        }
		
        final int specType = config.getAttribute(MODEL_BEHAVIOR_SPEC_TYPE, MODEL_BEHAVIOR_TYPE_DEFAULT);
        if ((specType != MODEL_BEHAVIOR_TYPE_NO_SPEC) && PERFORM_VALIDATION_BEFORE_LAUNCH.get()) {
            final Model model = config.getAdapter(Model.class);
            final IFile rootModule = model.getSpec().toSpec().getRootFile();
            final Validator.ValidationResult result;

            try (final InputStream is = rootModule.getContents()) {
            	result = Validator.validate(is);
            } catch (final IOException e) {
            	monitor.done();
            	
            	throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID, e.getMessage()));
            }
            
    		final MessageDialogWithToggle dialog;
            switch (result) {
            	case NO_PLUSCAL_EXISTS:
            	case NO_DIVERGENCE:
            		break;
            	case ERROR_ENCOUNTERED:
					dialog = MessageDialogWithToggle.openYesNoQuestion(
							PlatformUI.getWorkbench().getDisplay().getActiveShell(), "Error encountered",
							"Something went wrong attempting to detect divergence between PlusCal and its translation, continue anyway?",
							"Do not bug me about PlusCal verification during the rest of my Toolbox session.", false,
							null, null);
					
					if (dialog.getToggleState()) {
						PERFORM_VALIDATION_BEFORE_LAUNCH.set(false);
					}
					
					if (dialog.getReturnCode() == IDialogConstants.NO_ID) {
						return false;
					}
        			break;
            	case NO_TRANSLATION_EXISTS:
					dialog = MessageDialogWithToggle.openYesNoQuestion(
							PlatformUI.getWorkbench().getDisplay().getActiveShell(), "Translation missing",
							"Your spec appears to contain PlusCal but no TLA+ translation, are you sure you want to continue?",
							"Do not bug me about PlusCal verification during the rest of my Toolbox session.", false,
							null, null);
					
					if (dialog.getToggleState()) {
						PERFORM_VALIDATION_BEFORE_LAUNCH.set(false);
					}
					
					if (dialog.getReturnCode() == IDialogConstants.NO_ID) {
						return false;
					}
        			break;
            	case NO_CHECKSUMS_EXIST:
					dialog = MessageDialogWithToggle.openInformation(
							PlatformUI.getWorkbench().getDisplay().getActiveShell(), "A note about your spec",
							"Your spec contains PlusCal and a TLA+ translation - but they have not been verified to "
									+ "be in sync; consider re-translating the PlusCal algorithm.",
							"Do not bug me about PlusCal verification during the rest of my Toolbox session.", false,
							null, null);
					
					if (dialog.getToggleState()) {
						PERFORM_VALIDATION_BEFORE_LAUNCH.set(false);
					}

            		break;
            	case DIVERGENCE_EXISTS:
					dialog = MessageDialogWithToggle.openYesNoQuestion(
							PlatformUI.getWorkbench().getDisplay().getActiveShell(), "PlusCal out of sync",
							"The PlusCal and TLA+ translation in your spec appear to be out of sync - would you like to"
									+ " stop the launch?",
							"Do not bug me about PlusCal verification during the rest of my Toolbox session.", false,
							null, null);
					
					if (dialog.getToggleState()) {
						PERFORM_VALIDATION_BEFORE_LAUNCH.set(false);
					}
					
					if (dialog.getReturnCode() == IDialogConstants.YES_ID) {
						return false;
					}
            		break;
            }
        }
        
		try {
			monitor.beginTask("Reading model parameters", 1);
		} finally {
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
    	final Model model = config.getAdapter(Model.class);
    	
        // generate the model here
        int STEP = 100;

        try
        {
            monitor.beginTask("Creating model", 30);
            // step 1
            monitor.subTask("Creating directories");

            // retrieve the project containing the specification
            final IProject project = model.getSpec().getProject();
            if (project == null)
            {
                // project could not be found
                throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                        "Error accessing the spec project " + model.getSpec().getName()));
            }

            // retrieve the root file
            final IFile specRootFile = model.getSpec().getRootFile();
            if (specRootFile == null)
            {
                // root module file not found
                throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                        "Error accessing the root module " + model.getSpec().getRootFilename()));
            }

            // retrieve the model folder
            final IFolder modelFolder = model.getFolder();
            IPath targetFolderPath = modelFolder.getProjectRelativePath().addTrailingSeparator();

            // create the handles: MC.tla, MC.cfg and MC.out
            IFile tlaFile = project.getFile(targetFolderPath.append(ModelHelper.FILE_TLA));
            IFile cfgFile = project.getFile(targetFolderPath.append(ModelHelper.FILE_CFG));
            IFile outFile = project.getFile(targetFolderPath.append(ModelHelper.FILE_OUT));

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
                    final IResource[] checkpoints = config.getAdapter(Model.class).getCheckpoints(false);

                    // delete files
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
                                TLCActivator.logError("Error deleting a file " + members[i].getLocation(), e);
                            }
                        }
                    }
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
                        + model.getSpec().getRootFilename() + " into " + targetFolderPath.toOSString()));
            }
            
            // Copy the spec's root file userModule override if any.
            copyUserModuleOverride(monitor, 2, project, targetFolderPath, specRootFile);
            
            // get the list of dependent modules
            List extendedModules = ToolboxHandle.getExtendedModules(specRootFile.getName());

            // iterate and copy modules that are needed for the spec
            IFile moduleFile = null;
            for (int i = 0; i < extendedModules.size(); i++)
            {
                String module = (String) extendedModules.get(i);
				// Only take care of user modules and actually *linked* files
				// (not files defined via TLA_LIBRARY_PATH)
                if (ToolboxHandle.isUserModule(module) && ResourceHelper.isLinkedFile(project, module))
                {
                    moduleFile = ResourceHelper.getLinkedFile(project, module, false);
                    if (moduleFile != null)
                    {
						try {
	                        moduleFile.copy(targetFolderPath.append(moduleFile.getProjectRelativePath()), IResource.DERIVED
	                                | IResource.FORCE, new SubProgressMonitor(monitor, STEP / extendedModules.size()));
							copyUserModuleOverride(monitor, STEP / extendedModules.size(), project, targetFolderPath, moduleFile);
						} catch (ResourceException re) {
                    		// Trying to copy the file to the targetFolderPath produces an exception.
                    		// The most common cause is a dangling linked file in the .project metadata 
                    		// of the Toolbox project. Usually, a dangling link is the effect of copying
                    		// a single Toolbox project from one machine to the other missing modules 
                    		// extended (EXTENDS in TLA+) by a spec. The missing modules are part of
                    		// another spec which does not exist on the current machine.
                    		// We log the full exception to the Toolbox's error log (not directly visible
                    		// to the user) and raise an error dialog (see org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor).
                    		// We hint at how this problem can be addressed most of the time.
							TLCActivator.logError(
									String.format(
											"Error copying file %s to %s. Please correct the path to %s. \n(The first place to check is in the %s/.project file. Restart the Toolbox when you change the .project file.)",
											moduleFile.getLocation(), targetFolderPath, moduleFile.getName(),
											modelFolder.getRawLocation().removeLastSegments(1)), re);
							throw new CoreException(
									new Status(
											Status.ERROR,
											"org.lamport.tlc.toolbox.tool.tlc",
											String.format(
													"Error copying file %s to %s. Please correct the path to %s. \n(The first place to check is in the %s/.project file. Restart the Toolbox when you change the .project file.)",
													moduleFile.getLocation(), targetFolderPath, moduleFile.getName(),
													modelFolder.getRawLocation().removeLastSegments(1))));
                    	}
                    }
                    // TODO check the existence of copied files
                }
            }

            // create files
			for (int i = 0; i < files.length; i++) {
				if (files[i].exists()) {
					files[i].setContents(new ByteArrayInputStream("".getBytes()), IResource.DERIVED | IResource.FORCE,
							new SubProgressMonitor(monitor, 1));
				} else {
					files[i].create(new ByteArrayInputStream("".getBytes()), IResource.DERIVED | IResource.FORCE,
							new SubProgressMonitor(monitor, 1));
				}
			}

            monitor.worked(STEP);
            monitor.subTask("Creating contents");

            ModelWriter writer = new ModelWriter();
       
            // add the MODULE beginning and EXTENDS statement
            writer.addPrimer(ModelHelper.MC_MODEL_NAME, model.getSpec().getRootModuleName());

            // Sets constants to a Vector of the substitutions for the CONSTANT substitutions
            List<Assignment> constants = ModelHelper.deserializeAssignmentList(config.getAttribute(MODEL_PARAMETER_CONSTANTS,
                    new Vector<String>()));

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
            List<Assignment> overrides = ModelHelper.deserializeAssignmentList(config.getAttribute(MODEL_PARAMETER_DEFINITIONS,
                    new Vector<String>()));
            
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
           
            writer.addConstantExpressionEvaluation(model.getEvalExpression(), Model.MODEL_EXPRESSION_EVAL);

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
            	final String spec = config.getAttribute(MODEL_BEHAVIOR_CLOSED_SPECIFICATION, EMPTY_STRING);
    			if (model.getSpec().declares(spec) && !isExpression(spec)) {
            		writer.addFormulaList(spec, "SPECIFICATION", MODEL_BEHAVIOR_CLOSED_SPECIFICATION);
    			} else {
    				writer.addFormulaList(ModelWriter.createSourceContent(MODEL_BEHAVIOR_CLOSED_SPECIFICATION,
    						ModelWriter.SPEC_SCHEME, config), "SPECIFICATION", MODEL_BEHAVIOR_CLOSED_SPECIFICATION);
    			}
                break;
            case MODEL_BEHAVIOR_TYPE_SPEC_INIT_NEXT:
            	// the init and next formulas
            	final String init = config.getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT, EMPTY_STRING);
				if (model.getSpec().declares(init) && !isExpression(init)) {
            		writer.addFormulaList(init, "INIT", MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT);
            	} else {
            		writer.addFormulaList(ModelWriter.createSourceContent(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT,
            				ModelWriter.INIT_SCHEME, config), "INIT", MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT);
            	}
				
            	final String next = config.getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT, EMPTY_STRING);
				if (model.getSpec().declares(next) && !isExpression(next)) {
	           		writer.addFormulaList(next, "NEXT", MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT);
            	} else {
	                writer.addFormulaList(ModelWriter.createSourceContent(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT,
	                        ModelWriter.NEXT_SCHEME, config), "NEXT", MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT);
            	}
                break;
            }

            // // the specification name-formula pair
            // writer.addSpecDefinition(ModelHelper.createSpecificationContent(config),
            // MODEL_BEHAVIOR_CLOSED_SPECIFICATION);

            // do not write invariants and properties if there is no behavior spec
            if (hasSpec)
            {
            	// invariants (separate those declared in the spec from those declared in the model).
				final List<String> invariants = config.getAttribute(MODEL_CORRECTNESS_INVARIANTS, new Vector<String>());
				writer.addFormulaList(
						createProperties(writer, model.getSpec(), invariants, ModelWriter.INVARIANT_SCHEME),
						"INVARIANT", MODEL_CORRECTNESS_INVARIANTS);

				// properties
				final List<String> properties = config.getAttribute(MODEL_CORRECTNESS_PROPERTIES, new Vector<String>());
				writer.addFormulaList(createProperties(writer, model.getSpec(), properties, ModelWriter.PROP_SCHEME),
						"PROPERTY", MODEL_CORRECTNESS_PROPERTIES);
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
    
	private static boolean isExpression(final String formula) {
		// TLC's config file only accepts identifiers but no expressions
		// (tlc2.tool.ModelConfig.parse()). TLAplusParserTokenManager unfortunately does
		// not parse tokens such as "C!Spec" into an identifier. Subsequently this leads
		// to an invalid config. Thus, treat a formula with a bang as an expressions. If
		// tla+.jj ever gets changed to handle instantiated operators, this
		// workaround/hack can be removed.
		return formula.contains("!");
	}

	private static List<String[]> createProperties(final ModelWriter writer, final TLCSpec spec, final List<String> properties,
			final String scheme) {
		
		// Convert list of strings such as {"1Inv", "0x \in Nat"} into a subset of
		// checked formulas (prefixed with 1).
		final List<Formula> checkedFormula = ModelHelper.deserializeFormulaList(properties);

		// Create the input for the model writer out of all formula...
		final List<String[]> createFormulaListContent = ModelWriter.createFormulaListContentFormula(checkedFormula,
				scheme);

		// Collect those formula that are declared in the spec, not the MC.tla file.
		final List<Formula> declaredFormula = checkedFormula.stream().filter(f -> spec.declares(f.getFormula()) && !isExpression(f.getFormula()))
				.collect(Collectors.toList());

		// Override each declared formula with its original declaration. This will cause
		// ModelWriter.addFormulaList to omit it from the MC.tla file and only add it to MC.cfg.
		declaredFormula.forEach(f -> createFormulaListContent.set(checkedFormula.indexOf(f),
				new String[] { f.getFormula(), EMPTY_STRING, String.valueOf(checkedFormula.indexOf(f)) }));

		// createFormulaListContent has to be in the same order as checkedFormula.
		// Otherwise, TLCModelLaunchDataProvider.createError(TLCRegion,
		// String) would fail to match the violated invariant to the one stored in the
		// model. This results in the Toolbox reporting the wrong invariant. As a second
		// safeguard ModelWriter.createFormulaListContentFormula adds the formula's index
		// to the String[] which - if present - is eventually used as the formula's index
		// by ModelWriter.addFormulaList.
		return createFormulaListContent;
    }

	// Copy userModule overrides (see tlc2.tool.Spec.processSpec(SpecObj)) if
	// any. An override is an Java implementation of a user defined module. By
	// convention, the Java class file name has to be aligned with the module
	// name (i.e. Bits.tla -> Bits.class). For completeness, also copy the
	// Java source file from which the user manually compiled the class file.
	private void copyUserModuleOverride(IProgressMonitor monitor, int ticks, IProject project, IPath targetFolderPath,
			IFile tlaFile) throws CoreException {
		final IFile[] userModuleOverrides = ResourceHelper.getModuleOverrides(project, tlaFile);
		for (IFile userModuleOverride : userModuleOverrides) {
			try {
				userModuleOverride.copy(targetFolderPath.append(userModuleOverride.getProjectRelativePath()),
						IResource.DERIVED | IResource.FORCE, new SubProgressMonitor(monitor, ticks));
			} catch (CoreException e) {
				// If the file could not be copied, the link is obviously stale
				// and has to be removed to not create any problems in the
				// future. A link gets stale if e.g. the user removed the module
				// override manually in the file system.
				userModuleOverride.delete(true, monitor);
			}
		}
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

        final Model model = configuration.getAdapter(Model.class);
        final IFile rootModule = model.getTLAFile();

        monitor.worked(1);
        // parse the MC file
        IParseResult parseResult = ToolboxHandle.parseModule(rootModule, new SubProgressMonitor(monitor, 1), false,
                false);
        final Vector<TLAMarkerInformationHolder> detectedErrors = parseResult.getDetectedErrors();
        boolean status = !AdapterFactory.isProblemStatus(parseResult.getStatus());

        monitor.worked(1);
        // remove existing markers
        
        model.removeMarkers(Model.TLC_MODEL_ERROR_MARKER_SANY);
        monitor.worked(1);

        if (!detectedErrors.isEmpty())
        {
            TLCActivator.logDebug("Errors in model file found " + rootModule.getLocation());
        }

		final Map<TLAMarkerInformationHolder, Hashtable<String, Object>> props = sany2ToolboxErrors(monitor, rootModule,
				detectedErrors);
		props.values().forEach(marker -> model.setMarker(marker, Model.TLC_MODEL_ERROR_MARKER_SANY));

        if (MODE_GENERATE.equals(mode))
        {
            // generation is done
            // nothing to do more
            return false;
        } else
        {
            return status;
        }
    }

	protected Map<TLAMarkerInformationHolder, Hashtable<String, Object>> sany2ToolboxErrors(final IProgressMonitor monitor, final IFile rootModule,
			final Vector<TLAMarkerInformationHolder> detectedErrors) throws CoreException {
		FileEditorInput fileEditorInput = new FileEditorInput(rootModule);
        FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();
        final Map<TLAMarkerInformationHolder, Hashtable<String, Object>> result = new HashMap<>();
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
                        result.put(markerHolder, ModelHelper.createMarkerDescription(rootModule, document, searchAdapter,
                                message, severity, coordinates));
                    } else
                    {
                    	// see getLaunch(...) above
                    	DebugPlugin.getDefault().getLaunchManager().removeLaunch(this.launch);
                    	
                        // the reported error is not pointing to the MC file.
                        throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                                "Fatal error during validation of the model. "
                                        + "SANY discovered an error somewhere else than the MC file. "
                                        + "This is a bug. The error message was " + message + " in the module "
                                        + markerHolder.getModuleName()));
                    }
                } else
                {
                	// see getLaunch(...) above
                   	DebugPlugin.getDefault().getLaunchManager().removeLaunch(this.launch);
                   	
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
        return result;
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

        final Model model = config.getAdapter(Model.class);
        // retrieve the project containing the specification
        final IProject project = model.getSpec().getProject();
        if (project == null)
        {
            // project could not be found
            throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                    "Error accessing the spec project " + model.getSpec().getName()));
        }

        // setup the running flag
        // from this point any termination of the run must reset the
        // flag
        model.setRunning(true);

        // set the model to have the original trace shown
        model.setOriginalTraceShown(true);

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
        	job = new TLCProcessJob(model.getSpec().getName(), model.getName(), launch, numberOfWorkers);
            // The TLC job itself does not do any file IO
            job.setRule(mutexRule);
        } else {
        	if ("ad hoc".equalsIgnoreCase(cloud)) {
        		job = new DistributedTLCJob(model.getSpec().getName(), model.getName(), launch, numberOfWorkers);
                job.setRule(mutexRule);
        	} else {
        		numberOfWorkers = config.getAttribute(LAUNCH_DISTRIBUTED_NODES_COUNT, LAUNCH_DISTRIBUTED_NODES_COUNT_DEFAULT);
                //final IProject iproject = ResourceHelper.getProject(specName);
                final IFolder launchDir = model.getFolder();
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
					final DummyProcess process = new DummyProcess(launch);
					launch.addProcess(process);
					final TLCJobFactory factory = (TLCJobFactory) element
							.createExecutableExtension("clazz");
					final Properties props = new Properties();
					props.put(TLCJobFactory.MAIN_CLASS, tlc2.TLC.class.getName());
					// Add model and spec name to properties to make the model
					// checker run easily identifiable in the result email.
					props.put(TLCJobFactory.MODEL_NAME, model.getName());
					props.put(TLCJobFactory.SPEC_NAME, model.getSpec().getName());
					if (numberOfWorkers > 1) {
						props.put(TLCJobFactory.MAIN_CLASS, tlc2.tool.distributed.TLCServer.class.getName());
					}
					props.put(TLCJobFactory.MAIL_ADDRESS, config.getAttribute(
							LAUNCH_DISTRIBUTED_RESULT_MAIL_ADDRESS, "tlc@localhost"));

					final ExecutionStatisticsCollector udc = new ExecutionStatisticsCollector();
					if (udc.isEnabled()) {
						props.put(ExecutionStatisticsCollector.PROP, udc.getIdentifier());
					}
					
					// The parameters below are the only one currently useful with CloudDistributedTLC
					final StringBuffer tlcParams = new StringBuffer();
					
			        // fp seed offset (decrease by one to map from [1, 64] interval to [0, 63] array address)
					if (launch.getLaunchConfiguration().getAttribute(LAUNCH_FP_INDEX_RANDOM, LAUNCH_FP_INDEX_RANDOM_DEFAULT)) {
						final int fpIndex = new Random().nextInt(FP64.Polys.length);
						tlcParams.append("-fp");
			        	tlcParams.append(" ");
						tlcParams.append(String.valueOf(fpIndex));
					} else {
						final int fpSeedOffset = launch.getLaunchConfiguration().getAttribute(LAUNCH_FP_INDEX, LAUNCH_FP_INDEX_DEFAULT);
						tlcParams.append("-fp");
			        	tlcParams.append(" ");
						tlcParams.append(String.valueOf(fpSeedOffset));
					}
		        	tlcParams.append(" ");
			        
			        // add maxSetSize argument if not equal to the default
			        // code added by LL on 9 Mar 2012
			        final int maxSetSize = launch.getLaunchConfiguration().getAttribute(
			                LAUNCH_MAXSETSIZE, TLCGlobals.setBound);
			        if (maxSetSize != TLCGlobals.setBound) {
			        	tlcParams.append("-maxSetSize ");
			        	tlcParams.append(String.valueOf(maxSetSize));
			        	tlcParams.append(" ");
			        }
			        
			        // add -lncheck final if requested.
			        if (model.getAttribute(LAUNCH_DEFER_LIVENESS, false)) {
			        	tlcParams.append("-lncheck ");
			        	tlcParams.append("final");
			        	tlcParams.append(" ");
			        }
			        
			        boolean checkDeadlock = config.getAttribute(IModelConfigurationConstants.MODEL_CORRECTNESS_CHECK_DEADLOCK,
							IModelConfigurationDefaults.MODEL_CORRECTNESS_CHECK_DEADLOCK_DEFAULT);
					if (!checkDeadlock) {
						tlcParams.append("-deadlock");
					}

					job = factory.getTLCJob(cloud, file, numberOfWorkers, props, tlcParams.toString());
					job.addJobChangeListener(new WithStatusJobChangeListener(process, config.getAdapter(Model.class)));
					break;
				}
				// Notify the user that something went wrong and ask him to report it. This code path
				// is usually taken if the Toolbox distribution is incomplete. Thus, the exception should
				// never happen at the user's end. Anyway, try to give a clue what might be wrong.
                if (job == null) {
                	throw new CoreException(
                			new Status(
                					IStatus.ERROR,
                					TLCActivator.PLUGIN_ID,
                					String.format(
                							"The distribution mode '%s' selected in the \"How to run?\" section caused "
                									+ "an error. Check the Toolbox's \"Installation Details\" if the "
                									+ "'JCloud distributed TLC provider' is installed. If not, this is a bug "
                									+ "and should be reported to the Toolbox authors. Thank you for "
                									+ "your help and sorry for the inconvenience."
                									+ "\n\n"
                									+ "In the meantime, try running the Toolbox in non-distributed mode "
                									+ "by setting \"Run in distributed mode\" to 'off'. "
                									+ "You might have to 'Repair' your model via the \"Spec Explorer\" first.",
                									cloud)));
                	// "Repairing" the model here with ModelHelper.recoverModel(config) does not work. The 
                	// markers indicating a broken model have not been installed at this point.
                }
        	}
        }
        job.setPriority(Job.LONG);
        job.setUser(true);

        // setup the job change listener
        TLCJobChangeListener tlcJobListener = new TLCJobChangeListener(config.getAdapter(Model.class));
        job.addJobChangeListener(tlcJobListener);
        job.schedule();
    }
    
	// A DummyProcess instance has to be attached to the corresponding ILaunch
	// when the Job launched neither creates an IProcess nor IDebugTarget. In
    // this case the call to ILaunch#isTerminated will always evaluate to false
    // regardless of the real job's state.
	// Remember to call DummyProcess#setTerminated upon completion of the Job
	// with e.g. a IJobChangeListener.
	class DummyProcess implements IProcess {
		private final ILaunch launch;
		private boolean termiated = false;
		
		public DummyProcess(ILaunch aLaunch) {
			this.launch = aLaunch;
		}

		public void setTerminated() {
			this.termiated = true;
		}
		
		public void terminate() throws DebugException {
		}

		public boolean isTerminated() {
			return termiated;
		}

		public boolean canTerminate() {
			return !termiated;
		}

		public <T> T getAdapter(Class<T> adapter) {
			return null;
		}

		public String getAttribute(String key) {
			return null;
		}
		
		public void setAttribute(String key, String value) {
		}

		public IStreamsProxy getStreamsProxy() {
			return null;
		}

		public ILaunch getLaunch() {
			return launch;
		}

		public String getLabel() {
			return getClass().getSimpleName();
		}

		public int getExitValue() throws DebugException {
			return 0;
		}
	}

	// This opens up a dialog at the end of the job showing the status message
    class WithStatusJobChangeListener extends SimpleJobChangeListener {

		private final Model model;
		private final DummyProcess process;

		public WithStatusJobChangeListener(DummyProcess process, Model model) {
			this.process = process;
			this.model = model;
		}

		public void done(IJobChangeEvent event) {
			super.done(event);
	
			
			// TLC models seem to require some clean-up
			model.setRunning(false);
			model.recover();
			
			process.setTerminated();

			final IStatus status = event.getJob().getResult();
			final String message = status.getMessage();
			if (status instanceof ITLCJobStatus) {
				final ITLCJobStatus result = (ITLCJobStatus) status;
				
				if (result.isReconnect()) {
					// Do not open modal dialog if this is just a reconnect. In other words, no
					// dialog if user is running cloud TLC repeatedly.
					return;
				}
				
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
        private Model model;

        /**
         * Constructs the change listener
         * @param model the config to modify after the job completion
         */
        public TLCJobChangeListener(Model model)
        {
            this.model = model;
        }

        public void done(final IJobChangeEvent event)
        {
            super.done(event);

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
            final IFolder modelFolder = model.getFolder();
            WorkspaceJob refreshJob = new WorkspaceJob("") {

                public IStatus runInWorkspace(IProgressMonitor monitor) throws CoreException
                {
                	model.getCheckpoints(true);

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

				if (!Status.CANCEL_STATUS.equals(event.getJob().getResult()) && tlcJob.hasCrashed()) {
					// if TLC crashed with exit value > 0 and the user did *not*
					// click cancel, mark the job as crashed.
					model.setStale();
				}
            }
            model.setRunning(false);
 
            /* 
             * Lastly, take a snapshot of the finished spec. This provides a history of model checker runs.
             * Technically, snapshots are just regular models. However, their name has a specially crafted
             * suffix to identify it as a snapshot. The model for which it is a snapshot is identified by the
             * prefix of the snapshot's model name.
             */
            final int snapshotKeepCount = TLCActivator.getDefault().getPreferenceStore().getInt(TLCActivator.I_TLC_SNAPSHOT_KEEP_COUNT);
			if (!(snapshotKeepCount > 0) || model.isSnapshot()) {
				return;
			}
			refreshJob = new WorkspaceJob("Taking snapshot of " + model.getName() + "...") {
				public IStatus runInWorkspace(final IProgressMonitor monitor) throws CoreException {
					monitor.beginTask("Taking snapshot of " + model.getName() + "...", 1);
					final Model snapshot = model.snapshot();
					
					// If the result is an ITLCJobStatus, it means that TLC is running with Cloud
					// TLC. In other words, it is running remotely. Thus, we get the output from
					// the remote cloud instance and feed it to the regular Toolbox sinks.
					final IStatus status = event.getJob().getResult();
					if (status instanceof ITLCJobStatus) {
						
						snapshot.setRunningRemotely(true);
						
						final List<IProcessOutputSink> sinks = getProcessOutputSinks(snapshot);
						// Wrap in a job so that the parent job of which this joblistener is being
						// called can terminate. Otherwise, the model remains in model checking state.
						final Job j = new Job(
								String.format("Consuming output of Cloud TLC for model %s", model.getName())) {
							@Override
							protected IStatus run(IProgressMonitor monitor) {
								final ITLCJobStatus tlcJobStatus = (ITLCJobStatus) status;
								// Read the output provided by the status and send it to all sinks. The sinks
								// take care of updating the UI.
								final InputStream output = tlcJobStatus.getOutput();
								try {
									final BufferedReader in = new BufferedReader(
											new InputStreamReader(output));
									String line;
									while ((line = in.readLine()) != null) {
										// sinks expect a newline to correctly handle the line.
										for (IProcessOutputSink iProcessOutputSink : sinks) {
											iProcessOutputSink.appendText(line + "\n");
										}
										
										// Kill remote process when monitor gets c
										if (monitor.isCanceled() && !PlatformUI.getWorkbench().isClosing()) {
											tlcJobStatus.killTLC();
											return Status.OK_STATUS;
										}
									}
								} catch (IOException e) {
									if (e.getClass().getName()
											.equals("net.schmizz.sshj.transport.TransportException")) {
										// Indicates TLC process has terminated.
										return Status.OK_STATUS;
									}
									return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID, e.getMessage(), e);
								} finally {
									snapshot.setRunningRemotely(false);
								}
								return Status.OK_STATUS;
							}
							
							/* (non-Javadoc)
							 * @see org.eclipse.core.runtime.jobs.Job#belongsTo(java.lang.Object)
							 */
							@Override
							public boolean belongsTo(final Object family) {
								return snapshot == family;
							}

							@Override
							protected void canceling() {
								if (PlatformUI.getWorkbench().isClosing()) {
									// Do not terminate the remote instance when the Toolbox gets closed.
									super.canceling();
									return;
								}
								if (status instanceof ITLCJobStatus && snapshot.isRunningRemotely()) {
									final ITLCJobStatus tlcJobStatus = (ITLCJobStatus) status;
									tlcJobStatus.killTLC();
									snapshot.setRunningRemotely(false);
								}
								super.canceling();
							}
						};
						j.schedule();
					}
					monitor.done();
					return Status.OK_STATUS;
				}
				
				private List<IProcessOutputSink> getProcessOutputSinks(final Model snapshot) {
					final IConfigurationElement[] decls = Platform.getExtensionRegistry()
							.getConfigurationElementsFor(IProcessOutputSink.EXTENSION_ID);
					final List<IProcessOutputSink> sinks = new ArrayList<>(decls.length);
					for (int i = 0; i < decls.length; i++) {
						try {
							final IProcessOutputSink sink = (IProcessOutputSink) decls[i]
									.createExecutableExtension("class");
							sink.initializeSink(snapshot, IProcessOutputSink.TYPE_OUT);
							sinks.add(sink);
						} catch (CoreException e) {
							TLCActivator.logError("Error instatiating the IProcessSink extension", e);
						}
					}
					return sinks;
				}
			};
			refreshJob.setRule(model.getSpec().getProject());
			refreshJob.schedule();
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
