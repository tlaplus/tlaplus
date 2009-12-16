package org.lamport.tla.toolbox.tool.tlc.launch;

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
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.ILaunchConfigurationDelegate;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.tool.IParseResult;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.model.TypedSet;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelWriter;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.semantic.OpDefNode;

public class TraceExplorerDelegate extends TLCModelLaunchDelegate implements ILaunchConfigurationDelegate,
        IModelConfigurationConstants, IConfigurationConstants
{
    public static final String MODE_TRACE_EXPLORE = "exploreTrace";

    private static final String EMPTY_STRING = "";

    private TraceExpressionInformationHolder[] traceExpressionData;
    private IFile[] files;

    /**
     * Writes necessary information to TE.tla for parsing.
     */
    public boolean buildForLaunch(ILaunchConfiguration config, String mode, IProgressMonitor monitor)
            throws CoreException
    {

        int STEP = 100;

        // retrieve the project containing the specification
        IProject project = ResourceHelper.getProject(specName);
        IFolder modelFolder = project.getFolder(config.getAttribute(MODEL_NAME, EMPTY_STRING));
        if (!modelFolder.exists())
        {
            throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                    "Trace explorer was run and the model folder does not exist. This is a bug."));
        }
        IPath targetFolderPath = modelFolder.getProjectRelativePath().addTrailingSeparator();

        // create the handles: TE.tla, TE.cfg and TE.out
        IFile tlaFile = project.getFile(targetFolderPath.append(ModelHelper.TE_FILE_TLA));
        IFile cfgFile = project.getFile(targetFolderPath.append(ModelHelper.TE_FILE_CFG));
        IFile outFile = project.getFile(targetFolderPath.append(ModelHelper.TE_FILE_OUT));

        TLCActivator.logDebug("Writing files to: " + targetFolderPath.toOSString());

        files = new IFile[] { tlaFile, cfgFile, outFile };

        /*
         * We want to copy spec files to the model folder only if
         * the model is not locked. Before copying, the previous spec
         * files must be deleted.
         */
        if (!ModelHelper.isModelLocked(config))
        {

            /******************************************************************
             * This code deletes all existing files in the model folder except*
             * for the checkpoint folder, if it exists.                       *
             ******************************************************************/
            final IResource[] members = modelFolder.members();
            // erase everything inside
            if (members.length == 0)
            {
                monitor.worked(STEP);
            } else
            {
                // Get the checkpoint folder in order to avoid
                // deleting that folder.
                // This ModelHelper method should return an array of
                // size one because there should only be one checkpoint
                // folder.
                final IResource[] checkpoints = ModelHelper.getCheckpoints(config, false);

                ISchedulingRule deleteRule = ResourceHelper.getDeleteRule(members);

                // delete files
                ResourcesPlugin.getWorkspace().run(new IWorkspaceRunnable() {

                    public void run(IProgressMonitor monitor) throws CoreException
                    {

                        monitor.beginTask("Deleting files", members.length);
                        // delete the members of the target
                        // directory
                        for (int i = 0; i < members.length; i++)
                        {
                            try
                            {
                                if ((checkpoints.length > 0 && checkpoints[0].equals(members[i]))
                                        || members[i].getName().equals(ModelHelper.FILE_CFG)
                                        || members[i].getName().equals(ModelHelper.FILE_TLA)
                                        || members[i].getName().equals(ModelHelper.FILE_OUT))
                                {
                                    // We don't want to delete the checkpoints folder
                                    // or any of the MC files.
                                    continue;
                                }
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
                        monitor.done();
                    }
                }, deleteRule, IWorkspace.AVOID_UPDATE, new SubProgressMonitor(monitor, STEP));
            }
            /******************************************************************
             * Finished deleting files.                                       *
             ******************************************************************/

            /******************************************************************
             * This code copies all spec module files to the model folder.    *
             ******************************************************************/
            monitor.subTask("Copying files");

            // retrieve the root file
            IFile specRootFile = ResourceHelper.getLinkedFile(project, specRootFilename, false);
            if (specRootFile == null)
            {
                // root module file not found
                throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                        "Error accessing the root module " + specRootFilename));
            }

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

            ModelHelper.copyExtendedModuleFiles(specRootFile, targetFolderPath, monitor, STEP, project);

            /******************************************************************
             * Finished copying files.                                        *
             ******************************************************************/

        }

        /***************************************************************************
         * Create the TE.tla, TE.cfg, and TE.out files if they don't exist and set *
         * the contents equal to "".                                               *
         ***************************************************************************/
        ModelHelper.createOrClearFiles(files, monitor);

        /***************************************************************************
         * Now we write the appropriate contents to TE.tla and TE.cfg.             *
         * The following items are written to those files:                         *
         *                                                                         *
         * 1.) Name of module and EXTENDS specRootModule, TLC                    *
         * 2.) Variable declaration for each trace exploration expression          *
         * 3.) Definition of each trace exploration expression                     *
         * 4.) values of constants                                                 *
         * 5.) additional model values                                             *
         * 6.) additional definitions                                              *
         * 7.) definition overrides                                                *
         * 8.) Initial state predicate without trace exploration expression        *
         * 9.) Next state action without trace exploration expression              *
         *                                                                         *
         * The initial state predicate and next state action are written without   *
         * the trace exploration expressions because we don't know at this point if*
         * the expressions contain primed variables. We figure that out by parsing.*
         * We write the initial state predicate and next state action with the     *
         * variables from the original trace in order to detect any parse errors   *
         * caused by changes to the spec or model if the model is unlocked. For    *
         * example, the user could remove a variable from the spec. If the model is*
         * unlocked, the trace explorer will be run against the new version of the *
         * spec. This will cause a parse error that will be detected because the   *
         * initial state predicate will contain the variable that has been removed *
         * from the spec.                                                          *
         ***************************************************************************/
        monitor.worked(STEP);
        monitor.subTask("Creating contents");

        ModelWriter writer = new ModelWriter();

        // add extend primer
        writer.addPrimer(ModelHelper.TE_MODEL_NAME, ResourceHelper.getModuleName(specRootFilename));

        // variables and definitions for trace explorer expressions
        traceExpressionData = writer.addTraceExploreVariablesPreParse(ModelHelper.deserializeFormulaList(config
                .getAttribute(IModelConfigurationConstants.TRACE_EXPLORE_EXPRESSIONS, new Vector())),
                TRACE_EXPLORE_EXPRESSIONS);
        
        writeModelInfo(config, writer);

        // add the initial state predicate and next state action without
        // the trace exploration expressions in order to determine if they parse
        writer.addTraceStateDefsPreParse(config.getAttribute(
                IModelConfigurationConstants.TRACE_EXPLORE_INIT_STATE_CONJ, EMPTY_STRING), config.getAttribute(
                IModelConfigurationConstants.TRACE_EXPLORE_TRACE_ACTION_DISJ, EMPTY_STRING));

        monitor.worked(STEP);
        monitor.subTask("Writing contents");

        // Write the contents to the files
        writer.writeFiles(tlaFile, cfgFile, monitor);

        // do not want to rebuild the workspace
        return false;
    }

    /**
     * We use this method to check for parsing errors and to determine the level
     * of each trace explorer expression, i.e. whether there are primed variables or not.
     * If an expression is a temporal formula, this should show an error to the user.
     */
    public boolean finalLaunchCheck(ILaunchConfiguration configuration, String mode, IProgressMonitor monitor)
            throws CoreException
    {
        monitor.beginTask("Verifying model files", 4);

        IProject project = ResourceHelper.getProject(specName);
        IFolder launchDir = project.getFolder(modelName);
        IFile rootModule = launchDir.getFile(ModelHelper.TE_FILE_TLA);

        monitor.worked(1);
        // parse the TE.tla file
        IParseResult parseResult = ToolboxHandle.parseModule(rootModule, new SubProgressMonitor(monitor, 1), false,
                false);
        Assert
                .isTrue(parseResult instanceof ParseResult,
                        "Object returned by parsing the module is not an instance of ParseResult. This is not expected by the toolbox.");

        /***********************************************************************************
         * Check for parsing errors first.                                                 *
         ***********************************************************************************/
        if (parseResult.getDetectedErrors().size() > 0)
        {
            /*
             * This should appropriately display the parse error to the user.
             */
            
            

            // launch should not proceed
            return false;
        }

        /***********************************************************************************
         * There are no parsing errors. Now use the parse result to determine the level of *
         * each trace explorer expression, where the level indicates the TLA level of the  *  
         * expression as follows.                                                          *
         *                                                                                 *
         *   0 : Constant Level                                                            *               
         *   1 : State Level                                                               *                                       
         *   2 : Action Level                                                              *                                            
         *   3 : Temporal Level                                                            *
         *                                                                                 *
         * If an expression is level 3, this should cause an error to be displayed to the  *
         * user.                                                                           *
         ***********************************************************************************/
        /*
         * First get the OpDefNodes for the root module TE.tla
         * Put them in a hashtable for efficiency in retrieving them.
         */
        OpDefNode[] opDefNodes = ((ParseResult) parseResult).getSpecObj().getExternalModuleTable().getRootModule()
                .getOpDefs();
        Hashtable nodeTable = new Hashtable(opDefNodes.length);

        Assert.isNotNull(opDefNodes, "OpDefNodes[] from parsing TE.tla is null. This is a bug.");
        for (int j = 0; j < opDefNodes.length; j++)
        {
            String key = opDefNodes[j].getName().toString();
            nodeTable.put(key, opDefNodes[j]);
        }

        /*
         * Set the level for each trace expression using the corresponding OpDefNode
         */
        for (int i = 0; i < traceExpressionData.length; i++)
        {
            OpDefNode opDefNode = (OpDefNode) nodeTable.get(traceExpressionData[i].getIdentifier());
            traceExpressionData[i].setLevel(opDefNode.getBody().getLevel());
            // TODO check for temporal formulas (level 3)
        }

        /*************************************************************************************
         * Now clear the TE.tla and TE.cfg and write the correct contents to those files.    *
         * The following items are written to those files:                                   *
         *                                                                                   *
         * 1.) Name of module and EXTENDS specRootModule, TLC                                *
         * 2.) Variable declaration for each trace exploration expression                    *
         * 3.) Definition of each trace exploration expression                               *
         * 4.) values of constants                                                           *
         * 5.) additional model values                                                       *
         * 6.) additional definitions                                                        *
         * 7.) definition overrides                                                          *
         * 8.) Init and Next including trace explorer variables                              *
         *************************************************************************************/
        ModelHelper.createOrClearFiles(files, monitor);

        monitor.subTask("Creating contents");

        ModelWriter writer = new ModelWriter();

        // add extend primer
        writer.addPrimer(ModelHelper.TE_MODEL_NAME, ResourceHelper.getModuleName(specRootFilename));

        // variables and definitions for trace explorer expressions
        writer.addTraceExprVarDecsAndDefsPostParse(traceExpressionData, TRACE_EXPLORE_EXPRESSIONS);
        
        writeModelInfo(configuration, writer);
        
        
        String[] initContent = new String[]{};
        String[] nextContent = new String[]{};
        //writer.addFormulaList(initContent, "INIT", "traceExploreInit");
        //writer.addFormulaList(nextContent, "NEXT", "traceExploreNext");

        // launch should proceed
        return true;
    }

    public void launch(ILaunchConfiguration configuration, String mode, ILaunch launch, IProgressMonitor monitor)
            throws CoreException
    {
        // TODO Auto-generated method stub

    }

    /**
     * Writes constants, model values, new definitions, and overrides to the model writer.
     * 
     * @param config
     * @param writer
     * @throws CoreException
     */
    private void writeModelInfo(ILaunchConfiguration config, ModelWriter writer) throws CoreException
    {
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
    }

}
