package org.lamport.tla.toolbox.tool.tlc.job;

import java.io.ByteArrayInputStream;
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
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.core.runtime.jobs.MultiRule;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.action.Action;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.launch.ModelWriter;
import org.lamport.tla.toolbox.tool.tlc.model.TypedSet;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * Creates the model files
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelCreationJob extends AbstractJob implements IModelConfigurationConstants, IModelConfigurationDefaults
{

    private final ILaunchConfiguration config;
    private final String modelName;
    private final String specName;

    public ModelCreationJob(String specName, String modelName, ILaunchConfiguration config)
    {
        super("Model preparation for " + modelName);
        this.specName = specName;
        this.modelName = modelName;
        this.config = config;

    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.job.AbstractJob#getJobCompletedAction()
     */
    protected Action getJobCompletedAction()
    {
        return new Action() {
            public void run()
            {
                System.out.print("Model files created");
            }
        };
    }

    /* (non-Javadoc)
     * @see org.eclipse.core.runtime.jobs.Job#run(org.eclipse.core.runtime.IProgressMonitor)
     */
    protected IStatus run(IProgressMonitor monitor)
    {
        int STEP = 100;

        try
        {
            monitor.beginTask("Creating model", 30);

            monitor.subTask("Reading model parameters");
            final String specRootFilename = config.getAttribute(SPEC_ROOT_FILE, EMPTY_STRING);

            // step 1
            monitor.worked(1);
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
            if (modelFolder.exists())
            {
                // erase everything inside
                IResource[] members = modelFolder.members();
                if (members.length == 0)
                {
                    monitor.worked(STEP);
                } else
                {
                    for (int i = 0; i < members.length; i++)
                    {
                        members[i].delete(IResource.FORCE, new SubProgressMonitor(monitor, STEP / members.length));
                    }
                }
            } else
            {
                // create it
                modelFolder.create(IResource.DERIVED | IResource.FORCE, true, new SubProgressMonitor(monitor, STEP));
            }

            // create the lock
            // ModelHelper.createLock(modelName, modelFolder);

            // step 2
            IPath targetFolderPath = modelFolder.getProjectRelativePath().addTrailingSeparator();
            monitor.subTask("Copying files");

            specRootFile.copy(targetFolderPath.append(specRootFile.getProjectRelativePath()), IResource.DERIVED
                    | IResource.FORCE, new SubProgressMonitor(monitor, 1));
            IResource specRootFileCopy = modelFolder.findMember(specRootFile.getProjectRelativePath());
            if (specRootFileCopy == null)
            {
                throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID, "Error copying "
                        + specRootFilename + " into " + targetFolderPath.toOSString()));
            }
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
                }
            }

            // create the MC.tla, MC.cfg and MC.out
            final IFile tlaFile = project.getFile(targetFolderPath.append("MC").addFileExtension("tla"));
            final IFile cfgFile = project.getFile(targetFolderPath.append("MC").addFileExtension("cfg"));
            final IFile outFile = project.getFile(targetFolderPath.append("MC").addFileExtension("out"));

            ISchedulingRule createRule = MultiRule.combine(ResourceHelper.getCreateRule(outFile), MultiRule.combine(
                    ResourceHelper.getCreateRule(tlaFile), ResourceHelper.getCreateRule(cfgFile)));

            ResourcesPlugin.getWorkspace().run(new IWorkspaceRunnable() {

                public void run(IProgressMonitor monitor) throws CoreException
                {
                    // create the files
                    tlaFile.create(new ByteArrayInputStream("".getBytes()), IResource.DERIVED | IResource.FORCE,
                            new SubProgressMonitor(monitor, 1));
                    cfgFile.create(new ByteArrayInputStream("".getBytes()), IResource.DERIVED | IResource.FORCE,
                            new SubProgressMonitor(monitor, 1));
                    outFile.create(new ByteArrayInputStream("".getBytes()), IResource.DERIVED | IResource.FORCE,
                            new SubProgressMonitor(monitor, 1));
                }

            }, createRule, IWorkspace.AVOID_UPDATE, new SubProgressMonitor(monitor, STEP));

            System.out.println("Model TLA file is: " + tlaFile.getProjectRelativePath().toString());
            System.out.println("Model CFG file is: " + cfgFile.getProjectRelativePath().toString());
            System.out.println("Model OUT file is: " + outFile.getProjectRelativePath().toString());

            monitor.worked(STEP);
            monitor.subTask("Creating contents");

            ModelWriter writer = new ModelWriter();

            // add extend primer
            writer.addPrimer("MC", ResourceHelper.getModuleName(specRootFilename));

            // constants list
            List constants = ModelHelper.deserializeAssignmentList(config.getAttribute(MODEL_PARAMETER_CONSTANTS,
                    new Vector()));

            // the advanced model values
            TypedSet modelValues = TypedSet.parseSet(config.getAttribute(MODEL_PARAMETER_MODEL_VALUES, EMPTY_STRING));

            // add constants and model values
            writer.addConstants(constants, modelValues);

            // new definitions
            writer.addNewDefinitions(config.getAttribute(MODEL_PARAMETER_NEW_DEFINITIONS, EMPTY_STRING));

            // definition overrides list
            List overrides = ModelHelper.deserializeAssignmentList(config.getAttribute(MODEL_PARAMETER_DEFINITIONS,
                    new Vector()));
            writer.addFormulaList(ModelHelper.createOverridesContent(overrides, "def_ov"), "CONSTANT");

            // constraint
            writer.addFormulaList(ModelHelper.createSourceContent(MODEL_PARAMETER_CONSTRAINT, "constr", config),
                    "CONSTRAINT");
            // action constraint
            writer.addFormulaList(ModelHelper.createSourceContent(MODEL_PARAMETER_ACTION_CONSTRAINT, "action_constr",
                    config), "ACTION-CONSTRAINT");

            // the specification name-formula pair
            writer.addSpecDefinition(ModelHelper.createSpecificationContent(config));

            // invariants
            writer.addFormulaList(ModelHelper.createFormulaListContent(config.getAttribute(
                    MODEL_CORRECTNESS_INVARIANTS, new Vector()), "inv"), "INVARIANT");

            // properties
            writer.addFormulaList(ModelHelper.createFormulaListContent(config.getAttribute(
                    MODEL_CORRECTNESS_PROPERTIES, new Vector()), "prop"), "PROPERTY");

            monitor.worked(STEP);
            monitor.subTask("Writing contents");

            // write down the files
            writer.writeFiles(tlaFile, cfgFile, monitor);

            // refresh the model folder
            modelFolder.refreshLocal(IResource.DEPTH_ONE, new SubProgressMonitor(monitor, STEP));
            return Status.OK_STATUS;

        } catch (CoreException e)
        {
            e.printStackTrace();
            return e.getStatus();
        } finally
        {
            // make sure to complete the monitor
            monitor.done();
        }

    }

    public final ILaunchConfiguration getConfig()
    {
        return config;
    }
}
