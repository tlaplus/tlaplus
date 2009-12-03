package org.lamport.tla.toolbox.tool.tlc.util;

import java.util.Arrays;
import java.util.Comparator;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IMarkerDelta;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceRuleFactory;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Region;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.launch.TraceExplorerDelegate;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.st.Location;

/**
 * Provides utility methods for model manipulation
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelHelper implements IModelConfigurationConstants, IModelConfigurationDefaults
{

    /**
     * Empty location
     */
    public static final int[] EMPTY_LOCATION = new int[] { 0, 0, 0, 0 };

    /**
     * Marker indicating an error in the model
     */
    public static final String TLC_MODEL_ERROR_MARKER = "org.lamport.tla.toolbox.tlc.modelErrorMarker";
    /**
     * Marker indicating the TLC Errors
     */
    public static final String TLC_MODEL_ERROR_MARKER_TLC = "org.lamport.tla.toolbox.tlc.modelErrorTLC";
    /**
     * Marker indicating the SANY Errors
     */
    public static final String TLC_MODEL_ERROR_MARKER_SANY = "org.lamport.tla.toolbox.tlc.modelErrorSANY";

    public static final String TLC_MODEL_ERROR_MARKER_ATTRIBUTE_NAME = "attributeName";
    public static final String TLC_MODEL_ERROR_MARKER_ATTRIBUTE_IDX = "attributeIndex";

    /**
     * marker on .launch file with boolean attribute modelIsRunning 
     */
    public static final String TLC_MODEL_IN_USE_MARKER = "org.lamport.tla.toolbox.tlc.modelMarker";
    /**
     * marker on .launch file, binary semantics
     */
    public static final String TLC_CRASHED_MARKER = "org.lamport.tla.toolbox.tlc.crashedModelMarker";
    /**
     * model is being run
     */
    private static final String MODEL_IS_RUNNING = "modelIsRunning";
    /**
     * model is locked by a user lock
     */
    private static final String MODEL_IS_LOCKED = "modelIsLocked";
    /**
     * Delimiter used to serialize lists  
     */
    private static final String LIST_DELIMITER = ";";
    /**
     * Delimiter used to serialize parameter-value pair  
     */
    private static final String PARAM_DELIMITER = ":";

    public static final String MC_MODEL_NAME = "MC";
    public static final String FILE_TLA = MC_MODEL_NAME + ".tla";
    public static final String FILE_CFG = MC_MODEL_NAME + ".cfg";
    public static final String FILE_OUT = MC_MODEL_NAME + ".out";

    // trace explorer file names
    public static final String TE_MODEL_NAME = "TE";
    public static final String TE_FILE_TLA = TE_MODEL_NAME + ".tla";
    public static final String TE_FILE_CFG = TE_MODEL_NAME + ".cfg";
    public static final String TE_FILE_OUT = TE_MODEL_NAME + ".out";

    private static final String CHECKPOINT_STATES = MC_MODEL_NAME + ".st.chkpt";
    private static final String CHECKPOINT_QUEUE = "queue.chkpt";
    private static final String CHECKPOINT_VARS = "vars.chkpt";

    /**
     * Constructs the model called Foo___Model_1 from the SpecName Foo
     * if Foo___Model_1 already exists, delivers Foo___Model_2, and so on...
     * 
     * This method tests the existence of the launch configuration AND of the file
     * 
     * @param specProject
     * @return
     */
    public static String constructModelName(IProject specProject)
    {

        return doConstructModelName(specProject, "Model_1");
    }

    /**
     * Implementation of the {@link ModelHelper#constructModelName(IProject, String)}
     * @param specProject
     * @param proposition
     * @return
     */
    public static String doConstructModelName(IProject specProject, String proposition)
    {

        ILaunchConfiguration existingModel = getModelByName(specProject, proposition);
        if (existingModel != null || specProject.getFile(proposition + ".tla").exists())
        {
            String oldNumber = proposition.substring(proposition.lastIndexOf("_") + 1);
            int number = Integer.parseInt(oldNumber) + 1;
            proposition = proposition.substring(0, proposition.lastIndexOf("_") + 1);
            return doConstructModelName(specProject, proposition + number);
        }

        return proposition;
    }

    /**
     * Transforms a model name to the name visible to the user 
     * @param modelFile
     * @return
     */
    public static String getModelName(IFile modelFile)
    {
        String name = modelFile.getLocation().removeFileExtension().lastSegment();
        int i = name.indexOf(modelFile.getProject().getName() + "___");
        if (i != -1)
        {
            name = name.substring(i + (modelFile.getProject().getName() + "___").length());
        }
        return name;
    }

    /**
     * Convenience method retrieving the model for the project of the current specification
     * @param modelName name of the model
     * @return launch configuration or null, if not found
     */
    public static ILaunchConfiguration getModelByName(String modelName)
    {
        return getModelByName(ToolboxHandle.getCurrentSpec().getProject(), modelName);
    }

    /**
     * Retrieves the model name by name
     * @param specProject
     * @param modelName
     * @return ILaunchConfiguration representing a model or null
     */
    public static ILaunchConfiguration getModelByName(IProject specProject, String modelName)
    {
        // a model name can be "spec__modelname" or just "modelname"
        if (modelName.indexOf(specProject.getName() + "___") != 0)
        {
            modelName = specProject.getName() + "___" + modelName;
        }

        if (modelName.endsWith(".launch"))
        {
            modelName = modelName.substring(0, modelName.length() - ".launch".length());
        }

        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
        ILaunchConfigurationType launchConfigurationType = launchManager
                .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_CONFIGURATION_TYPE);

        try
        {
            ILaunchConfiguration[] launchConfigurations = launchManager
                    .getLaunchConfigurations(launchConfigurationType);
            for (int i = 0; i < launchConfigurations.length; i++)
            {

                if (launchConfigurations[i].getName().equals(modelName))
                {
                    return launchConfigurations[i];
                }
            }

        } catch (CoreException e)
        {
            TLCActivator.logError("Error finding the model name", e);
        }

        return null;
    }

    /**
     * Given the model name, this will search for a
     * ILaunchConfiguration that is used to launch
     * the trace explorer. If it does not exist, it
     * creates the configuration file.
     * 
     * @param modelName 
     * @return
     */
    public static ILaunchConfiguration getTraceExploreConfigByName(String modelName)
    {

        String configName = ToolboxHandle.getCurrentSpec().getName() + "___" + modelName + "___TE";

        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
        ILaunchConfigurationType configType = launchManager
                .getLaunchConfigurationType(TraceExplorerDelegate.LAUNCH_CONFIGURATION_TYPE);

        ILaunchConfiguration config = null;

        try
        {
            // check if it has been created
            ILaunchConfiguration[] configs;

            configs = launchManager.getLaunchConfigurations(configType);
            for (int i = 0; i < configs.length; i++)
            {
                if (configs[i].getName().equals(configName))
                {
                    config = configs[i];
                    return config;
                }
            }

            // configuration file does not exist, so create it
            IFolder modelFolder = ToolboxHandle.getCurrentSpec().getProject().getFolder(modelName);
            // IFolder traceFolder = modelFolder.getFolder(modelName);
            // if (!traceFolder.exists())
            // {
            // traceFolder.create(IResource.DERIVED | IResource.FORCE, true, new NullProgressMonitor());
            // }

            ILaunchConfigurationWorkingCopy launchCopy = configType.newInstance(modelFolder, configName);
            return launchCopy.doSave();

        } catch (CoreException e)
        {
            TLCActivator.logError("Bug finding a trace explorer launch file for model " + modelName + ".", e);
        }

        Assert.isNotNull(config, "Could not find or create launch file for trace explorer for model " + modelName
                + ". This is a bug.");
        return config;

    }

    public static String getTraceExploreLaunchConfigName(String modelName)
    {
        return ToolboxHandle.getCurrentSpec().getName() + "___" + modelName + "___TE";
    }

    /**
     * Convenience method
     * @param modelFile file containing the model
     * @return ILaunchconfiguration
     */
    public static ILaunchConfiguration getModelByFile(IFile modelFile)
    {
        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
        return launchManager.getLaunchConfiguration(modelFile);
    }

    /**
     * Saves the config working copy
     * @param config
     */
    public static void doSaveConfigurationCopy(ILaunchConfigurationWorkingCopy config)
    {
        try
        {
            config.doSave();
        } catch (CoreException e)
        {
            TLCActivator.logError("Error saving the model", e);
        }
    }

    /**
     * Creates a serial version of the assignment list, to be stored in the {@link ILaunchConfiguration}
     * 
     * Any assignment consist of a label, parameter list and the right side
     * These parts are serialized as a list with delimiter {@link ModelHelper#LIST_DELIMETER}
     * The parameter list is stored as a list with delimiter {@link ModelHelper#PARAM_DELIMITER}
     * 
     * If the assignment is using a model value {@link Assignment#isModelValue()} == <code>true, the right
     * side is set to the label resulting in (foo = foo) 
     * 
     *   
     */
    public static List serializeAssignmentList(List assignments)
    {
        Iterator iter = assignments.iterator();
        Vector result = new Vector(assignments.size());

        StringBuffer buffer;
        while (iter.hasNext())
        {
            Assignment assign = (Assignment) iter.next();

            buffer = new StringBuffer();

            // label
            buffer.append(assign.getLabel()).append(LIST_DELIMITER);

            // parameters if any
            for (int j = 0; j < assign.getParams().length; j++)
            {
                String param = assign.getParams()[j];
                if (param != null)
                {
                    buffer.append(param);
                }
                buffer.append(PARAM_DELIMITER);
            }
            buffer.append(LIST_DELIMITER);

            // right side
            // encode the model value usage (if model value is set, the assignment right side is equals to the label)

            if (assign.getRight() != null)
            {
                buffer.append(assign.getRight());
            }

            // isModelValue
            buffer.append(LIST_DELIMITER).append((assign.isModelValue() ? "1" : "0"));

            // is symmetrical
            buffer.append(LIST_DELIMITER).append((assign.isSymmetricalSet() ? "1" : "0"));

            result.add(buffer.toString());
        }
        return result;
    }

    /**
     * De-serialize assignment list. 
     * @see ModelHelper#serializeAssignmentList(List)
     */
    public static List deserializeAssignmentList(List serializedList)
    {
        Vector result = new Vector(serializedList.size());
        Iterator iter = serializedList.iterator();
        String[] fields = new String[] { null, "", "", "0", "0" };
        while (iter.hasNext())
        {
            String[] serFields = ((String) iter.next()).split(LIST_DELIMITER);
            System.arraycopy(serFields, 0, fields, 0, serFields.length);

            String[] params;
            if ("".equals(fields[1]))
            {
                params = new String[0];
            } else
            {
                params = fields[1].split(PARAM_DELIMITER);
            }
            // assignment with label as right side are treated as model values
            Assignment assign = new Assignment(fields[0], params, fields[2]);

            // is Model Value
            if (fields.length > 3 && fields[3].equals("1"))
            {
                assign.setModelValue(true);

                // is symmetrical
                if (fields.length > 4 && fields[4].equals("1"))
                {
                    assign.setSymmetric(true);
                }
            }

            result.add(assign);
        }
        return result;
    }

    /**
     * De-serialize formula list, to a list of formulas, that are selected (have a leading "1")
     * 
     * The first character of the formula is used to determine if the formula is enabled in the model 
     * editor or not. This allows the user to persist formulas, which are not used in the current model 
     */
    public static List deserializeFormulaList(List serializedList)
    {
        Vector result = new Vector(serializedList.size());
        Iterator serializedIterator = serializedList.iterator();
        while (serializedIterator.hasNext())
        {
            String entry = (String) serializedIterator.next();
            Formula formula = new Formula(entry.substring(1));
            if ("1".equals(entry.substring(0, 1)))
            {
                result.add(formula);
            }
        }
        return result;
    }

    /**
     * Extract the constants from module node
     * @param moduleNode
     * @return a list of assignments
     */
    public static List createConstantsList(ModuleNode moduleNode)
    {
        OpDeclNode[] constantDecls = moduleNode.getConstantDecls();
        Vector constants = new Vector(constantDecls.length);
        for (int i = 0; i < constantDecls.length; i++)
        {
            String[] params = new String[constantDecls[i].getNumberOfArgs()];
            // pre-fill the empty array
            Arrays.fill(params, EMPTY_STRING);
            Assignment assign = new Assignment(constantDecls[i].getName().toString(), params, EMPTY_STRING);
            constants.add(assign);
        }
        return constants;
    }

    /**
     * Checks whether the constant defined by assignment is defined in the module node
     * @param assignment
     * @param node
     * @return
     */
    public static boolean hasConstant(Assignment assignment, ModuleNode moduleNode)
    {
        OpDeclNode[] constantDecls = moduleNode.getConstantDecls();
        for (int i = 0; i < constantDecls.length; i++)
        {
            if (assignment.getLabel().equals(constantDecls[i].getName().toString())
                    && assignment.getParams().length == constantDecls[i].getNumberOfArgs())
            {
                return true;
            }
        }
        return false;
    }

    /**
     * Extract the variables from module node
     * @param moduleNode
     * @return a string representation of the variables
     * 
     * This method is being called with moduleNode = null when the model is
     * saved when the spec is unparsed.  I added a hack to handle that case,
     * but I'm not positive that there are no further problems that this can
     * cause.  LL. 20 Sep 2009
     */
    public static String createVariableList(ModuleNode moduleNode)
    {
        if (moduleNode == null)
        {
            return "";
        }
        StringBuffer buffer = new StringBuffer();
        OpDeclNode[] variableDecls = moduleNode.getVariableDecls();
        for (int i = 0; i < variableDecls.length; i++)
        {
            buffer.append(variableDecls[i].getName().toString());
            if (i != variableDecls.length - 1)
            {
                buffer.append(", ");
            }
        }
        return buffer.toString();
    }

    /*
     * Returns an array of Strings containing the variables declared
     * in the module.  Added 10 Sep 2009 by LL & DR
     */
    public static String[] createVariableArray(ModuleNode moduleNode)
    {
        OpDeclNode[] variableDecls = moduleNode.getVariableDecls();
        String[] returnVal = new String[variableDecls.length];
        for (int i = 0; i < variableDecls.length; i++)
        {
            returnVal[i] = variableDecls[i].getName().toString();
        }
        return returnVal;
    }

    /*
     * Returns true iff the specified module declares
     * at least one variable.  Added 10 Sep 2009 by LL & DR
     */
    public static boolean hasVariables(ModuleNode moduleNode)
    {
        OpDeclNode[] variableDecls = moduleNode.getVariableDecls();
        return variableDecls.length > 0;
    }

    public static SymbolNode getSymbol(String name, ModuleNode moduleNode)
    {
        return moduleNode.getContext().getSymbol(name);
    }

    /**
     * Extract the operator definitions from module node
     * @param moduleNode
     * @return a list of assignments
     */
    public static List createDefinitionList(ModuleNode moduleNode)
    {
        OpDefNode[] operatorDefinitions = moduleNode.getOpDefs();

        Vector operations = new Vector(operatorDefinitions.length);
        for (int i = 0; i < operatorDefinitions.length; i++)
        {
            String[] params = new String[operatorDefinitions[i].getNumberOfArgs()];
            // pre-fill the empty array
            Arrays.fill(params, "");
            Assignment assign = new Assignment(operatorDefinitions[i].getName().toString(), params, "");
            operations.add(assign);
        }
        return operations;
    }

    /**
     * This method eventually changes the constants list. If the signature constants of both
     * lists are equal, the constants list is left untouched. Otherwise, all constants not present
     * in the constantsFromModule are removed, and all missing are added.
     * <br>
     * For constant comparison {@link Assignment#equalSignature(Assignment)} is used
     * 
     * @param constants the list with constants, eventually the subject of change
     * @param constantsFromModule a list of constants from the module (no right side, no params)
     */
    public static List mergeConstantLists(List constants, List constantsFromModule)
    {
        Vector constantsToAdd = new Vector();
        Vector constantsUsed = new Vector();
        Vector constantsToDelete = new Vector();

        // iterate over constants from module
        for (int i = 0; i < constantsFromModule.size(); i++)
        {
            Assignment fromModule = (Assignment) constantsFromModule.get(i);
            // find it in the module list
            boolean found = false;

            for (int j = 0; j < constants.size(); j++)
            {
                Assignment constant = (Assignment) constants.get(j);
                if (fromModule.equalSignature(constant))
                {
                    // store the information that the constant is used
                    constantsUsed.add(constant);
                    found = true;
                    break;
                }
            }
            // constant is in the module but not in the model
            if (!found)
            {
                // save the constant for adding later
                constantsToAdd.add(fromModule);
            }
        }

        // add all
        constantsToDelete.addAll(constants);
        // remove all used
        constantsToDelete.removeAll(constantsUsed);

        // at this point, all used constants are in the constantUsed list
        constants.retainAll(constantsUsed);

        // all constants to add are in constantsTo Add list
        constants.addAll(constantsToAdd);

        return constantsToDelete;
    }

    /**
     * Retrieves the editor with model instance opened, or null, if no editor found
     * @param model
     * @return
     */
    public static IEditorPart getEditorWithModelOpened(ILaunchConfiguration model)
    {
        return UIHelper.getActivePage().findEditor(new FileEditorInput(model.getFile()));
    }

    /**
     * Retrieves the working directory for the model
     * <br>Note, this is a handle operation only, the resource returned may not exist
     * @param config 
     * @return the Folder.
     */
    public static IFolder getModelTargetDirectory(ILaunchConfiguration config)
    {
        Assert.isNotNull(config);
        Assert.isTrue(config.getFile().exists());
        return (IFolder) config.getFile().getProject().findMember(getModelName(config.getFile()));
    }

    /**
     * Retrieves a file where the log of the TLC run is written
     * @param config configuration representing the model
     * @return the file handle, or null
     */
    public static IFile getModelOutputLogFile(ILaunchConfiguration config)
    {
        Assert.isNotNull(config);
        IFolder targetFolder = ModelHelper.getModelTargetDirectory(config);
        if (targetFolder != null && targetFolder.exists())
        {
            IFile logFile = (IFile) targetFolder.findMember(ModelHelper.FILE_OUT);
            if (logFile != null && logFile.exists())
            {
                return logFile;
            }
        }

        return null;
    }

    /**
     * Retrieves the TLA file that is being model checked on the model run
     * @param config configuration representing the model
     * @return a file handle or <code>null</code>
     */
    public static IFile getModelTLAFile(ILaunchConfiguration config)
    {
        Assert.isNotNull(config);
        IFolder targetFolder = ModelHelper.getModelTargetDirectory(config);
        if (targetFolder != null && targetFolder.exists())
        {
            IFile mcFile = (IFile) targetFolder.findMember(ModelHelper.FILE_TLA);
            if (mcFile != null && mcFile.exists())
            {
                return mcFile;
            }
        }
        return null;
    }

    /**
     * Installs a model modification change listener  
     * @param provider provider for the file representing the model
     * @param runnable a runnable to run if the model is changed 
     */
    public static IResourceChangeListener installModelModificationResourceChangeListener(final IFileProvider provider,
            final Runnable runnable)
    {
        // construct the listener
        IResourceChangeListener listener = new IResourceChangeListener() {
            public void resourceChanged(IResourceChangeEvent event)
            {
                // get the marker changes
                IMarkerDelta[] markerChanges = event.findMarkerDeltas(TLC_MODEL_IN_USE_MARKER, false);

                // usually this list has at most one element
                for (int i = 0; i < markerChanges.length; i++)
                {
                    if (provider.getResource(IFileProvider.TYPE_MODEL).equals(markerChanges[i].getResource()))
                    {
                        UIHelper.runUIAsync(runnable);
                    }
                }
            }
        };

        // add to the workspace root
        ResourcesPlugin.getWorkspace().addResourceChangeListener(listener, IResourceChangeEvent.POST_CHANGE);

        // return the listener
        return listener;
    }

    /**
     * Checks whether the model is running or not
     * @param config
     * @return
     * @throws CoreException
     */
    public static boolean isModelRunning(ILaunchConfiguration config) throws CoreException
    {
        // marker
        IFile resource = config.getFile();
        if (resource.exists())
        {
            IMarker marker;
            IMarker[] foundMarkers = resource.findMarkers(TLC_MODEL_IN_USE_MARKER, false, IResource.DEPTH_ZERO);
            if (foundMarkers.length > 0)
            {
                marker = foundMarkers[0];
                // remove trash if any
                for (int i = 1; i < foundMarkers.length; i++)
                {
                    foundMarkers[i].delete();
                }

                return marker.getAttribute(MODEL_IS_RUNNING, false);
            } else
            {
                return false;
            }
        } else
        {
            return false;
        }
        /*
        // persistence property
        String isLocked = config.getFile().getPersistentProperty(new QualifiedName(TLCActivator.PLUGIN_ID, MODEL_IS_RUNNING));
        if (isLocked == null) 
        {
            return false;
        } else {
            return Boolean.getBoolean(isLocked);
        }
        */

        /*
        return config.getAttribute(MODEL_IS_RUNNING, false);
        */
    }

    /**
     * Checks whether the model is locked or not
     * @param config
     * @return
     * @throws CoreException
     */
    public static boolean isModelLocked(ILaunchConfiguration config) throws CoreException
    {
        // marker
        IFile resource = config.getFile();
        if (resource.exists())
        {
            IMarker marker;
            IMarker[] foundMarkers = resource.findMarkers(TLC_MODEL_IN_USE_MARKER, false, IResource.DEPTH_ZERO);
            if (foundMarkers.length > 0)
            {
                marker = foundMarkers[0];
                // remove trash if any
                for (int i = 1; i < foundMarkers.length; i++)
                {
                    foundMarkers[i].delete();
                }

                return marker.getAttribute(MODEL_IS_LOCKED, false);
            } else
            {
                return false;
            }
        } else
        {
            return false;
        }
        /*
        // persistence property
        String isLocked = config.getFile().getPersistentProperty(new QualifiedName(TLCActivator.PLUGIN_ID, MODEL_IS_RUNNING));
        if (isLocked == null) 
        {
            return false;
        } else {
            return Boolean.getBoolean(isLocked);
        }
        */

        /*
        return config.getAttribute(MODEL_IS_RUNNING, false);
        */
    }

    /**
     * Looks up if the model has a stale marker. The stale marker is installed in case,
     * if the model is locked, but no TLC is running on this model.
     * @param config
     * @return
     * @throws CoreException
     */
    public static boolean isModelStale(ILaunchConfiguration config) throws CoreException
    {
        // marker
        IFile resource = config.getFile();
        if (resource.exists())
        {
            IMarker[] foundMarkers = resource.findMarkers(TLC_CRASHED_MARKER, false, IResource.DEPTH_ZERO);
            if (foundMarkers.length > 0)
            {
                return true;
            } else
            {
                return false;
            }
        } else
        {
            return false;
        }
    }

    /**
     * Tries to recover model after an abnormal TLC termination
     * It deletes all temporary files on disk and restores the state to unlocked.
     * @param config
     */
    public static void recoverModel(ILaunchConfiguration config) throws CoreException
    {
        IFile resource = config.getFile();
        if (resource.exists())
        {
            // remove any crashed markers
            IMarker[] foundMarkers = resource.findMarkers(TLC_CRASHED_MARKER, false, IResource.DEPTH_ZERO);
            if (foundMarkers.length == 0)
            {
                return;
            }

            ModelHelper.cleanUp(config);

            for (int i = 0; i < foundMarkers.length; i++)
            {
                foundMarkers[i].delete();
            }

            foundMarkers = resource.findMarkers(TLC_MODEL_IN_USE_MARKER, false, IResource.DEPTH_ZERO);
            for (int i = 0; i < foundMarkers.length; i++)
            {
                foundMarkers[i].delete();
            }
        }
    }

    /**
     * Cleans up the TLC working directory
     * @param config
     */
    private static void cleanUp(ILaunchConfiguration config) throws CoreException
    {

    }

    /**
     * Signals that the model is staled
     */
    public static void staleModel(ILaunchConfiguration config) throws CoreException
    {
        config.getFile().createMarker(TLC_CRASHED_MARKER);
    }

    /**
     * Signals the start of model execution
     * @param config
     * @param isRunning whether TLC is running on the config or not
     */
    public static void setModelRunning(ILaunchConfiguration config, boolean isRunning) throws CoreException
    {
        IFile resource = config.getFile();
        if (resource.exists())
        {
            IMarker marker;
            IMarker[] foundMarkers = resource.findMarkers(TLC_MODEL_IN_USE_MARKER, false, IResource.DEPTH_ZERO);
            if (foundMarkers.length > 0)
            {
                marker = foundMarkers[0];
                // remove trash if any
                for (int i = 1; i < foundMarkers.length; i++)
                {
                    foundMarkers[i].delete();
                }
            } else
            {
                marker = resource.createMarker(TLC_MODEL_IN_USE_MARKER);
            }

            marker.setAttribute(MODEL_IS_RUNNING, isRunning);
        }
        /*
        // persistence property
        config.getFile().setPersistentProperty(new QualifiedName(TLCActivator.PLUGIN_ID, MODEL_IS_RUNNING), Boolean.toString(true));
         */

        /*
        // file modification 
        ModelHelper.writeAttributeValue(config, IModelConfigurationConstants.MODEL_IS_RUNNING, true);
         */
    }

    /**
     * Signals that the model is locked if isLocked is true, signals that
     * the model is unlocked if isLocked is false
     * @param config
     * @param lock whether the model should be locked or not
     * @throws CoreException
     */
    public static void setModelLocked(ILaunchConfiguration config, boolean lock) throws CoreException
    {
        IFile resource = config.getFile();
        if (resource.exists())
        {
            IMarker marker;
            IMarker[] foundMarkers = resource.findMarkers(TLC_MODEL_IN_USE_MARKER, false, IResource.DEPTH_ZERO);
            if (foundMarkers.length > 0)
            {
                marker = foundMarkers[0];
                // remove trash if any
                for (int i = 1; i < foundMarkers.length; i++)
                {
                    foundMarkers[i].delete();
                }
            } else
            {
                marker = resource.createMarker(TLC_MODEL_IN_USE_MARKER);
            }

            marker.setAttribute(MODEL_IS_LOCKED, lock);
        }
        /*
        // persistence property
        config.getFile().setPersistentProperty(new QualifiedName(TLCActivator.PLUGIN_ID, MODEL_IS_RUNNING), Boolean.toString(true));
         */

        /*
        // file modification 
        ModelHelper.writeAttributeValue(config, IModelConfigurationConstants.MODEL_IS_RUNNING, true);
         */
    }

    /**
     * Signals the end of model execution
     * 
     * This method is no longer used.
     * TODO remove
     * 
     * User unlock will unlock any model. An automatic unlock caused by the end of 
     * a run of TLC will only unlock the model if there is no user lock on that model.
     * @param config
     * @param userLock true if this is caused by the user explicitly unlocking the model
     * by clicking the lock button, false if this is caused automatically by the end
     * of TLC
     * @deprecated
     */
    public static void unlockModel(ILaunchConfiguration config, boolean userUnlock) throws CoreException
    {
        IFile resource = config.getFile();
        if (config.exists())
        {
            IMarker marker;
            IMarker[] foundMarkers = resource.findMarkers(TLC_MODEL_IN_USE_MARKER, false, IResource.DEPTH_ZERO);
            if (foundMarkers.length > 0)
            {
                marker = foundMarkers[0];
                // remove trash if any
                for (int i = 1; i < foundMarkers.length; i++)
                {
                    foundMarkers[i].delete();
                }
            } else
            {
                marker = resource.createMarker(TLC_MODEL_IN_USE_MARKER);
            }

            if (userUnlock)
            {
                // user unlock always unlocks the model
                marker.setAttribute(MODEL_IS_RUNNING, false);
                marker.setAttribute(MODEL_IS_LOCKED, false);
            } else if (!marker.getAttribute(MODEL_IS_LOCKED, false))
            {
                // automatic unlock only unlocks the model
                // if there is not a user lock on that model
                marker.setAttribute(MODEL_IS_RUNNING, false);
                marker.setAttribute(MODEL_IS_LOCKED, false);
            }

        }
        /*
        // persistence property
        config.getFile().setPersistentProperty(new QualifiedName(TLCActivator.PLUGIN_ID, MODEL_IS_RUNNING), Boolean.toString(false));
        */

        /*
        // file modification 
        ModelHelper.writeAttributeValue(config, IModelConfigurationConstants.MODEL_IS_RUNNING, false);
        */
    }

    /**
     * Write a boolean value into the launch config and saves it
     * @param config
     * @param attributeName
     * @param value
     */
    public static void writeAttributeValue(ILaunchConfiguration config, String attributeName, boolean value)
            throws CoreException
    {
        ILaunchConfigurationWorkingCopy copy;
        if (config instanceof ILaunchConfigurationWorkingCopy)
        {
            copy = (ILaunchConfigurationWorkingCopy) config;
        } else
        {
            copy = config.getWorkingCopy();
        }

        copy.setAttribute(attributeName, value);
        copy.doSave();
    }

    /**
     * Simple interface for getting a resource 
     */
    public static interface IFileProvider
    {
        public static final int TYPE_MODEL = 1;
        public static final int TYPE_RESULT = 2;

        public IFile getResource(int type);
    }

    /**
     * Remove a model marker of a particular type
     * @param configuration the model to remove markers from
     * @param type the marker type
     */
    public static void removeModelProblemMarkers(ILaunchConfiguration configuration, String type)
    {
        System.out.println("entering removeModelProblemMarkers() on " + configuration.getName()
                + " with markerType set to " + type);
        try
        {
            IMarker[] foundMarkers = configuration.getFile().findMarkers(type, true, IResource.DEPTH_ONE);
            for (int i = 0; i < foundMarkers.length; i++)
            {
                foundMarkers[i].delete();
            }
        } catch (CoreException e)
        {
            TLCActivator.logError("Error removing model markers", e);
        }
    }

    /**
     * Delete all model error markers from a resource
     * @param configuration the model to remove markers from
     */
    public static void removeModelProblemMarkers(ILaunchConfiguration configuration)
    {
        removeModelProblemMarkers(configuration, TLC_MODEL_ERROR_MARKER);
    }

    /**
     * Installs a marker on the model
     * @param resource the model file to install markers on
     * @param map a map with attributes
     */
    public static IMarker installModelProblemMarker(IResource resource, Map properties, String markerType)
    {
        Assert.isNotNull(resource);
        Assert.isTrue(resource.exists());

        try
        {
            // create an empty marker
            IMarker marker = resource.createMarker(markerType);
            marker.setAttributes(properties);
            return marker;
        } catch (CoreException e)
        {
            TLCActivator.logError("Error installing a model marker", e);
        }

        return null;
    }

    /**
     * For an given id that is used in the document retrieves the four coordinates of it's first occurrence.
     * @param document
     * @param searchAdapter
     * @param idRegion
     * @return location coordinates in the sense of {@link Location} class (bl, bc, el, ec).
     * @throws CoreException on errors
     */
    public static int[] calculateCoordinates(IDocument document, FindReplaceDocumentAdapter searchAdapter, String id)
            throws CoreException
    {
        try
        {
            IRegion foundId = searchAdapter.find(0, id, true, true, false, false);
            if (foundId == null)
            {
                return EMPTY_LOCATION;
            } else
            {
                // return the coordinates
                return regionToLocation(document, foundId, true);
            }
        } catch (BadLocationException e)
        {
            throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                    "Error during detection of the id position in MC.tla.", e));
        }
    }

    /**
     * Converts four-int-location to a region
     * TODO: unit test!
     * @param document
     * @param location
     * @return
     * @throws BadLocationException 
     */
    public static IRegion locationToRegion(IDocument document, Location location) throws BadLocationException
    {
        int offset = document.getLineOffset(location.beginLine() - 1) + location.beginColumn() - 1;
        int length = document.getLineOffset(location.endLine() - 1) + location.endColumn() - offset;
        return new Region(offset, length);
    }

    /**
     * Recalculate region in a document to four-int-coordinates
     * @param document
     * @param region
     * @param singleLine true, if the region covers one line only
     * @return four ints: begin line, begin column, end line, end column
     * @throws BadLocationException
     */
    public static int[] regionToLocation(IDocument document, IRegion region, boolean singleLine)
            throws BadLocationException
    {
        if (!singleLine)
        {
            throw new IllegalArgumentException("Not implemented");
        }

        int[] coordinates = new int[4];
        // location of the id found in the provided document
        int offset = region.getOffset();
        int length = region.getLength();
        // since the id is written as one word, we are in the same line
        coordinates[0] = document.getLineOfOffset(offset) + 1; // begin line
        coordinates[2] = document.getLineOfOffset(offset) + 1; // end line

        // the columns are relative to the offset of the line
        IRegion line = document.getLineInformationOfOffset(offset);
        coordinates[1] = offset - line.getOffset(); // begin column
        coordinates[3] = coordinates[1] + length; // end column

        // return the coordinates
        return coordinates;
    }

    /**
     * Create a map with marker parameters
     * @param config 
     * @param errorMessage
     * @param severityError
     * @return
     */
    public static Hashtable createMarkerDescription(String errorMessage, int severity)
    {
        Hashtable prop = new Hashtable();

        prop.put(IMarker.SEVERITY, new Integer(severity));
        prop.put(IMarker.MESSAGE, errorMessage);
        prop.put(TLC_MODEL_ERROR_MARKER_ATTRIBUTE_NAME, EMPTY_STRING);
        prop.put(TLC_MODEL_ERROR_MARKER_ATTRIBUTE_IDX, new Integer(0));
        prop.put(IMarker.LOCATION, EMPTY_STRING);
        prop.put(IMarker.CHAR_START, new Integer(0));
        prop.put(IMarker.CHAR_END, new Integer(0));
        return prop;
    }

    /**
     * Using the supplied findReplaceAdapter finds the name of the attribute 
     * (saved in the comment, previous to the region in which the error has been detected) 
     * 
     * @param configuration the configuration of the launch
     * @param document the document of the file containing the generated model .tla file
     * @param searchAdapter the search adapter on the document
     * @param message the error message
     * @param severity the error severity
     * @param coordinates coordinates in the document describing the area that is the id
     * 
     * @return a map object containing the information required for the marker installation:
     * <ul>
     *  <li>IMarker.SEVERITY</li>
     *  <li>IMarker.MESSAGE</li>
     *  <li>TLC_MODEL_ERROR_MARKER_ATTRIBUTE_NAME</li>
     *  <li>TLC_MODEL_ERROR_MARKER_ATTRIBUTE_IDX</li>
     *  <li>IMarker.LOCATION</li>
     *  <li>IMarker.CHAR_START</li>
     *  <li>IMarker.CHAR_END</li>
     * </ul> 
     * @throws CoreException if something goes wrong
     */
    public static Hashtable createMarkerDescription(ILaunchConfiguration configuration, IDocument document,
            FindReplaceDocumentAdapter searchAdapter, String message, int severity, int[] coordinates)
            throws CoreException
    {
        String attributeName;
        Region errorRegion = null;
        int attributeIndex = -1;
        try
        {
            // find the line in the document
            IRegion lineRegion = document.getLineInformation(coordinates[0] - 1);
            if (lineRegion != null)
            {
                int errorLineOffset = lineRegion.getOffset();

                // find the previous comment
                IRegion commentRegion = searchAdapter.find(errorLineOffset, ModelWriter.COMMENT, false, false, false,
                        false);

                // find the next separator
                IRegion separatorRegion = searchAdapter.find(errorLineOffset, ModelWriter.SEP, true, false, false,
                        false);
                if (separatorRegion != null && commentRegion != null)
                {
                    // find the first attribute inside of the
                    // comment
                    IRegion attributeRegion = searchAdapter.find(commentRegion.getOffset(), ModelWriter.ATTRIBUTE
                            + "[a-z]*[A-Z]*", true, false, false, true);
                    if (attributeRegion != null)
                    {
                        // get the attribute name without the
                        // attribute marker
                        attributeName = document.get(attributeRegion.getOffset(), attributeRegion.getLength())
                                .substring(ModelWriter.ATTRIBUTE.length());

                        // find the index
                        IRegion indexRegion = searchAdapter.find(attributeRegion.getOffset()
                                + attributeRegion.getLength(), ModelWriter.INDEX + "[0-9]+", true, false, false, true);
                        if (indexRegion != null && indexRegion.getOffset() < separatorRegion.getOffset())
                        {
                            // index value found
                            String indexString = document.get(indexRegion.getOffset(), indexRegion.getLength());
                            if (indexString != null && indexString.length() > 1)
                            {
                                try
                                {
                                    attributeIndex = Integer.parseInt(indexString.substring(1));
                                } catch (NumberFormatException e)
                                {
                                    throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                                            "Error during detection of the error position in MC.tla."
                                                    + "Error parsing the attribute index. " + message, e));
                                }
                            }
                        } else
                        {
                            // no index
                        }

                        // the first character of the next line
                        // after the comment

                        IRegion firstBlockLine = document.getLineInformation(document.getLineOfOffset(commentRegion
                                .getOffset()) + 1);
                        int beginBlockOffset = firstBlockLine.getOffset();
                        // get the user input
                        if (attributeName.equals(MODEL_PARAMETER_NEW_DEFINITIONS))
                        {
                            // there is no identifier in this
                            // block
                            // the user input starts directly
                            // from the first character
                        } else
                        {
                            // the id-line representing the
                            // identifier "id_number ==" comes
                            // first
                            // the user input starts only on the
                            // second line
                            // so adding the length of the
                            // id-line
                            beginBlockOffset = beginBlockOffset + firstBlockLine.getLength() + 1;
                        }

                        // calculate the error region

                        // end line coordinate
                        if (coordinates[2] == 0)
                        {
                            // not set
                            // mark one char starting from the
                            // begin column
                            errorRegion = new Region(errorLineOffset + coordinates[1] - beginBlockOffset, 1);
                        } else if (coordinates[2] == coordinates[0])
                        {
                            // equals to the begin line
                            // mark the actual error region
                            int length = coordinates[3] - coordinates[1];

                            errorRegion = new Region(errorLineOffset + coordinates[1] - beginBlockOffset,
                                    (length == 0) ? 1 : length);
                        } else
                        {
                            // the part of the first line from
                            // the begin column to the end
                            int summedLength = lineRegion.getLength() - coordinates[1];

                            // iterate over all full lines
                            for (int l = coordinates[0] + 1; l < coordinates[2]; l++)
                            {
                                IRegion line = document.getLineInformation(l - 1);
                                summedLength = summedLength + line.getLength();
                            }
                            // the part of the last line to the
                            // end column
                            summedLength += coordinates[3];

                            errorRegion = new Region(errorLineOffset + coordinates[1] - beginBlockOffset, summedLength);
                        }

                        // install the marker showing the
                        // information in the corresponding
                        // attribute (and index), at the given place

                    } else
                    {
                        // problem could not detect attribute
                        throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                                "Error during detection of the error position in MC.tla."
                                        + "Could not detect the attribute. " + message));
                    }
                } else
                {
                    // problem could not detect block
                    throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                            "Error during detection of the error position in MC.tla."
                                    + "Could not detect definition block. " + message));
                }
            } else
            {
                // problem could not detect line
                throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                        "Error during detection of the error position in MC.tla."
                                + "Could not data on specified location. " + message));
            }
        } catch (BadLocationException e)
        {
            throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                    "Error during detection of the error position in MC.tla." + "Accessing MC.tla file failed. "
                            + message, e));
        }

        // If the message refers to module MC, this should be replaced with
        // the location in the model.
        message = getMessageWithoutMC(message, attributeName, attributeIndex);

        // create the return object
        Hashtable props = new Hashtable();
        props.put(IMarker.SEVERITY, new Integer(severity));
        props.put(IMarker.MESSAGE, message);
        props.put(TLC_MODEL_ERROR_MARKER_ATTRIBUTE_NAME, attributeName);
        props.put(TLC_MODEL_ERROR_MARKER_ATTRIBUTE_IDX, new Integer(attributeIndex));
        props.put(IMarker.LOCATION, "");
        props.put(IMarker.CHAR_START, new Integer(errorRegion.getOffset()));
        props.put(IMarker.CHAR_END, new Integer(errorRegion.getOffset() + errorRegion.getLength()));

        return props;
    }

    /**
     * This method takes an error message generated by SANY for the
     * MC.tla file and attempts to remove the mention of the MC file and insert
     * the name of the model attribute and location within that attribute
     * where the parse error occured.
     * 
     * For example, the location in the message returned by SANY that says
     * "at line 25, column 2 in module MC" will be replaced with something
     * like "in Definition Overrides, line 2".
     * 
     * It is definitely possible that the set of expressions searched for by this method
     * is not exhaustive, so some messages will remain the same even if they mention the
     * MC file.
     * 
     * @param message the SANY error message for the MC file
     * @param attributeName the name of the model attribute where the error occured
     * @param attributeIndex the 0-based index of the error within the model attribute.
     * For example, if the second definition override caused an error, the attributeIndex
     * should be 1. It can be -1 if no index is found, in which case no information about
     * the location within the model attribute will be included in the message.
     * @return the message without MC location information and with model location information
     */
    private static String getMessageWithoutMC(String message, String attributeName, int attributeIndex)
    {
        if (message.indexOf("in module MC") != -1 || message.indexOf("of module MC") != -1)
        {
            // first possible expression
            String[] splitMessage = message.split("at line [0-9]{1,}, column [0-9]{1,} in module MC", 2);
            if (splitMessage.length != 2)
            {
                // split around other possibility
                splitMessage = message.split(
                        "line [0-9]{1,}, col [0-9]{1,} to line [0-9]{1,}, col [0-9]{1,} of module MC", 2);
            }
            if (splitMessage.length == 2)
            {
                String toReturn = splitMessage[0] + " in " + getSectionNameFromAttributeName(attributeName);
                if (attributeIndex != -1)
                {
                    // the exact location is known
                    toReturn = toReturn + " at line " + (attributeIndex + 1);
                }
                return toReturn + splitMessage[1];
            } else
            {
                // cannot find expression containing MC module
                // even though it is in the message
                return message;
            }
        } else
        {
            return message;
        }
    }

    /**
     * This gets the title of the section in the model editor
     * corresponding to the attributeName.
     * 
     * @param attributeName
     * @return
     */
    private static String getSectionNameFromAttributeName(String attributeName)
    {
        if (attributeName.equals(MODEL_CORRECTNESS_INVARIANTS))
        {
            return "Invariants";
        } else if (attributeName.equals(MODEL_CORRECTNESS_PROPERTIES))
        {
            return "Properties";
        } else if (attributeName.equals(MODEL_PARAMETER_ACTION_CONSTRAINT))
        {
            return "Action Contraint";
        } else if (attributeName.equals(MODEL_PARAMETER_CONSTRAINT))
        {
            return "Constraint";
        } else if (attributeName.equals(MODEL_PARAMETER_CONSTANTS))
        {
            return "What is the model?";
        } else if (attributeName.equals(MODEL_PARAMETER_DEFINITIONS))
        {
            return "Definition Override";
        } else if (attributeName.equals(MODEL_PARAMETER_NEW_DEFINITIONS))
        {
            return "Additional Definitions";
        } else if (attributeName.equals(MODEL_PARAMETER_MODEL_VALUES))
        {
            return "Model Values";
        } else if (attributeName.equals(MODEL_BEHAVIOR_CLOSED_SPECIFICATION))
        {
            return "Temporal formula";
        } else if (attributeName.equals(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT))
        {
            return "Init";
        } else if (attributeName.equals(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT))
        {
            return "Next";
        } else if (attributeName.equals(MODEL_PARAMETER_VIEW))
        {
            return "View";
        } else if (attributeName.equals(MODEL_EXPRESSION_EVAL))
        {
            return "Expression";
        }
        return attributeName;
    }

    /**
     * Retrieves error markers of the model
     * @param config
     * @return
     * @throws CoreException
     */
    public static IMarker[] getModelProblemMarker(ILaunchConfiguration config) throws CoreException
    {
        IFile resource = config.getFile();
        if (resource.exists())
        {
            IMarker[] foundMarkers = resource.findMarkers(TLC_MODEL_ERROR_MARKER, true, IResource.DEPTH_ZERO);
            return foundMarkers;
        }

        return new IMarker[0];
    }

    /**
     * Checks whether the checkpoint files exist for a given model
     * If doRefresh is set to true, this method will refresh the model directory,
     * and if a checkpoint folder is found, it will refresh the contents of that folder.
     * This means that the eclipse workspace representation of that directory will
     * synch with the file system. This is a long running job, so this method should not
     * be called within the run method of another job unless the scheduling rule for
     * refreshing the model directory is included in the scheduling rule of the job which
     * is calling this method. This scheduling rule can be found by calling
     * {@link IResourceRuleFactory#refreshRule(IResource)}
     * @param config
     * @param doRefresh whether the model directory's contents and any checkpoint
     * folders contents should be refreshed
     * @return the array of checkpoint directories, sorted from last to first
     */
    public static IResource[] getCheckpoints(ILaunchConfiguration config, boolean doRefresh) throws CoreException
    {
        // yy-MM-dd-HH-mm-ss
        Pattern pattern = Pattern.compile("[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}");

        Vector checkpoints = new Vector();
        IFolder directory = getModelTargetDirectory(config);

        if (directory != null && directory.exists())
        {
            // refreshing is necessary because TLC creates
            // the checkpoint folders, but they may not have
            // been incorporated into the toolbox workspace
            // yet
            // the depth is one to find any checkpoint folders
            if (doRefresh)
            {
                directory.refreshLocal(IResource.DEPTH_ONE, null);
            }
            IResource[] members = directory.members();
            for (int i = 0; i < members.length; i++)
            {
                if (members[i].getType() == IResource.FOLDER)
                {
                    Matcher matcher = pattern.matcher(members[i].getName());
                    if (matcher.matches())
                    {
                        // if there is a checkpoint folder, it is necessary
                        // to refresh its contents because they may not
                        // be part of the workspace yet
                        if (doRefresh)
                        {
                            members[i].refreshLocal(IResource.DEPTH_ONE, null);
                        }
                        if (((IFolder) members[i]).findMember(CHECKPOINT_QUEUE) != null
                                && ((IFolder) members[i]).findMember(CHECKPOINT_VARS) != null
                                && ((IFolder) members[i]).findMember(CHECKPOINT_STATES) != null)
                        {
                            checkpoints.add(members[i]);
                        }
                    }
                }
            }
        }
        IResource[] result = (IResource[]) checkpoints.toArray(new IResource[checkpoints.size()]);
        // sort the result
        Arrays.sort(result, new Comparator() {
            public int compare(Object arg0, Object arg1)
            {
                return ((IResource) arg0).getName().compareTo(((IResource) arg1).getName());
            }
        });

        return result;
    }

    /**
     * Find the IDs in the given text and return the array of 
     * regions pointing to those or an empty array, if no IDs were found.
     * An ID is scheme_timestamp, created by {@link ModelWriter#getValidIdentifier(String)} e.G. next_125195338522638000
     * @param text text containing IDs (error text)
     * @return array of regions or empty array
     */
    public static IRegion[] findIds(String text)
    {
        return ModelWriter.findIds(text);
    }

    /**
     * Finds the locations in the given text and return the array of 
     * regions pointing to those or an empty array, if no location were found.
     * A location is a pointer in the TLA file, e.G. "line 11, col 8 to line 14, col 26 of module Foo"
     * @param text text containing locations (error text)
     * @return array of regions or empty array
     */
    public static IRegion[] findLocations(String text)
    {
        if (text == null || text.length() == 0)
        {
            return new IRegion[0];
        }

        Matcher matcher = Location.LOCATION_MATCHER.matcher(text);
        Vector regions = new Vector();
        while (matcher.find())
        {
            regions.add(new Region(matcher.start(), matcher.end() - matcher.start()));
        }
        // look for this pattern also
        // this pattern appears when there
        // is an error evaluating a nested expression
        matcher = Location.LOCATION_MATCHER4.matcher(text);
        while (matcher.find())
        {
            regions.add(new Region(matcher.start(), matcher.end() - matcher.start()));
        }
        return (IRegion[]) regions.toArray(new IRegion[regions.size()]);
    }

    /**
     * Returns the OpDefNode with name equal to input string
     * Returns null if there is no such OpDefNode
     * @param name
     * @return
     */
    public static OpDefNode getOpDefNode(String name)
    {
        SpecObj specObj = ToolboxHandle.getCurrentSpec().getValidRootModule();
        /*
         * SpecObj can be null if the spec is unparsed.
         */
        if (specObj != null)
        {
            OpDefNode[] opDefNodes = specObj.getExternalModuleTable().getRootModule().getOpDefs();
            for (int j = 0; j < opDefNodes.length; j++)
            {
                if (opDefNodes[j].getName().toString().equals(name))
                {
                    return opDefNodes[j];
                }
            }
        }
        return null;
    }

    /**
     * Checks, whether a model attribute is a list 
     * @param attributeName name of the attribute, see {@link IModelConfigurationConstants}
     * @return true for invariants, properties, constants and definition overriders
     */
    public static boolean isListAttribute(String attributeName)
    {
        if (attributeName != null
                && (attributeName.equals(IModelConfigurationConstants.MODEL_CORRECTNESS_INVARIANTS)
                        || attributeName.equals(IModelConfigurationConstants.MODEL_CORRECTNESS_PROPERTIES)
                        || attributeName.equals(IModelConfigurationConstants.MODEL_PARAMETER_CONSTANTS) || attributeName
                        .equals(IModelConfigurationConstants.MODEL_PARAMETER_DEFINITIONS)))
        {
            return true;
        }
        return false;
    }

    /**
     * A convenience method for access to the root module node
     * @return a module or null, if spec not parsed
     */
    public static ModuleNode getRootModuleNode()
    {
        SpecObj specObj = ToolboxHandle.getSpecObj();
        if (specObj != null)
        {
            return specObj.getExternalModuleTable().getRootModule();
        }
        return null;
    }
}
