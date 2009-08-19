package org.lamport.tla.toolbox.tool.tlc.util;

import java.util.Arrays;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
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
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.jface.text.Region;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SymbolNode;

/**
 * Provides utility methods for model manipulation
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelHelper implements IModelConfigurationConstants, IModelConfigurationDefaults
{
    /**
     * Marker indicating an error in the model
     */
    public static final String TLC_MODEL_ERROR_MARKER = "org.lamport.tla.toolbox.tlc.modelErrorMarker";

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
     * Delimiter used to serialize lists  
     */
    private static final String LIST_DELIMITER = ";";
    /**
     * Delimiter used to serialize parameter-value pair  
     */
    private static final String PARAM_DELIMITER = ":";
    /**
     * Counter to be able to generate unique identifiers
     */
    private static long globalCounter = 1;

    public static final String MC_MODEL_NAME = "MC";
    public static final String FILE_TLA = MC_MODEL_NAME + ".tla";
    public static final String FILE_CFG = MC_MODEL_NAME + ".cfg";
    public static final String FILE_OUT = MC_MODEL_NAME + ".out";

    private static final String CHECKPOINT_STATES = MC_MODEL_NAME + ".st.chkpt";
    private static final String CHECKPOINT_QUEUE =  "queue.chkpt";
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
        if (modelName.indexOf(specProject.getName()) != 0) 
        {
            modelName = specProject.getName() + "___" + modelName;
        } 
        
        if (modelName.endsWith(".launch" ))
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
    private static List deserializeFormulaList(List serializedList)
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
     * Create a representation of the behavior formula
     * @param config launch configuration
     * @return a string array containing two strings: name of the formula, and the formula with the name
     * @throws CoreException if something went wrong
     */
    public static String[] createSpecificationContent(ILaunchConfiguration config) throws CoreException
    {
        StringBuffer buffer = new StringBuffer();
        String identifier = getValidIdentifier("spec");
        String[] result = null;

        // the identifier
        buffer.append(identifier).append(" ==\n");

        int specType = config.getAttribute(MODEL_BEHAVIOR_SPEC_TYPE, MODEL_BEHAVIOR_TYPE_DEFAULT);

        switch (specType) {
        case MODEL_BEHAVIOR_TYPE_NO_SPEC:
            // no spec - nothing to do

            break;
        case MODEL_BEHAVIOR_TYPE_SPEC_CLOSED:
            // append the closed formula
            buffer.append(config.getAttribute(MODEL_BEHAVIOR_CLOSED_SPECIFICATION, EMPTY_STRING));
            result = new String[] { identifier, buffer.toString() };
            break;
        case MODEL_BEHAVIOR_TYPE_SPEC_INIT_NEXT:
            // init, next, fairness
            String modelInit = config.getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT, EMPTY_STRING);
            String modelNext = config.getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT, EMPTY_STRING);
            String vars = config.getAttribute(MODEL_BEHAVIOR_VARS, EMPTY_STRING);

            String modelFairness = config.getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_FAIRNESS, EMPTY_STRING);
            // append init. next, fairness
            buffer.append(modelInit).append(" /\\[][ ").append(modelNext).append(" ]_").append("<<").append(vars)
                    .append(">> ");
            // add fairness condition, if any
            if (!EMPTY_STRING.equals(modelFairness))
            {
                buffer.append(" /\\ ").append(modelFairness);
            }

            result = new String[] { identifier, buffer.toString() };
            break;
        default:
            break;
        }

        // specification
        // to .cfg : <id>
        // to _MC.tla : <id> == <expression>
        // : <id> == <init> /\[][<next>]_vars /\ <fairness>
        return result;
    }

    /**
     * Create the content for a single source element
     * @return a list with at most one String[] element
     * @throws CoreException 
     */
    public static List createSourceContent(String propertyName, String labelingScheme, ILaunchConfiguration config)
            throws CoreException
    {
        Vector result = new Vector();
        String value = config.getAttribute(propertyName, EMPTY_STRING);
        if (EMPTY_STRING.equals(value))
        {
            return result;
        }
        String identifier = getValidIdentifier(labelingScheme);
        StringBuffer buffer = new StringBuffer();

        // the identifier
        buffer.append(identifier).append(" ==\n");
        buffer.append(value);

        result.add(new String[] { identifier, buffer.toString() });
        return result;
    }

    /**
     * Converts formula list to a string representation
     * @param serializedFormulaList, list of strings representing formulas (with enablement flag)
     * @param labelingScheme
     * @return
     */
    public static List createFormulaListContent(List serializedFormulaList, String labelingScheme)
    {
        List formulaList = ModelHelper.deserializeFormulaList(serializedFormulaList);
        return (createListContent(formulaList, labelingScheme));
    }

    /**
     * Create a list of overrides
     * @param overrides
     * @param string
     * @return
     */
    public static List createOverridesContent(List overrides, String labelingScheme)
    {
        Vector resultContent = new Vector(overrides.size());
        String[] content;
        String id;
        Assignment formula;
        for (int i = 0; i < overrides.size(); i++)
        {
            id = getValidIdentifier(labelingScheme);
            // formulas
            // to .cfg : <id>
            // to _MC.tla : <id> == <expression>
            formula = ((Assignment) overrides.get(i));
            content = new String[] { formula.getLabel() + " <- " + id,
                    formula.getParametrizedLabel(id) + " ==\n" + formula.getRight() };
            resultContent.add(content);
        }
        return resultContent;
    }

    /**
     * Converts formula list to a string representation
     * @param formulaList list of assignments
     * @param labelingScheme 
     * @return
     */
    public static List createListContent(List formulaList, String labelingScheme)
    {
        Vector resultContent = new Vector(formulaList.size());
        String[] content;
        String label;
        for (int i = 0; i < formulaList.size(); i++)
        {
            label = getValidIdentifier(labelingScheme);
            // formulas
            // to .cfg : <id>
            // to _MC.tla : <id> == <expression>
            content = new String[] { label, label + " ==\n" + ((Formula) formulaList.get(i)).getFormula() };
            resultContent.add(content);
        }
        return resultContent;
    }

    /**
     * Retrieves new valid (not used) identifier from given schema
     * @param schema a naming schema
     * @return a valid identifier
     */
    public static synchronized String getValidIdentifier(String schema)
    {
        try
        {
            Thread.sleep(10);
        } catch (InterruptedException e)
        {
        }
        return schema + "_" + System.currentTimeMillis() + 1000 * (++globalCounter);
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
            Arrays.fill(params, "");
            Assignment assign = new Assignment(constantDecls[i].getName().toString(), params, "");
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
     */
    public static String createVariableList(ModuleNode moduleNode)
    {
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
     * @param config config representing the model
     * @return the file handle, or null
     */
    public static IFile getModelOutputLogFile(ILaunchConfiguration config)
    {
        Assert.isNotNull(config);
        IFolder targetFolder = ModelHelper.getModelTargetDirectory(config);
        if (targetFolder !=null && targetFolder.exists())
        {
            IFile logFile = (IFile) targetFolder.findMember(ModelHelper.FILE_OUT);
            if (logFile.exists())
            {
                return logFile;
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
        // TODO
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
     */
    public static void lockModel(ILaunchConfiguration config) throws CoreException
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

            marker.setAttribute(MODEL_IS_RUNNING, true);
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
     * @param config
     */
    public static void unlockModel(ILaunchConfiguration config) throws CoreException
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

            marker.setAttribute(MODEL_IS_RUNNING, false);
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
     * Delete all model error markers from a resource
     * @param configuration the model to remove markers from
     */
    public static void removeModelProblemMarkers(ILaunchConfiguration configuration)
    {
        try
        {
            IMarker[] foundMarkers = configuration.getFile().findMarkers(TLC_MODEL_ERROR_MARKER, false,
                    IResource.DEPTH_ONE);
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
     * Installs a marker on the model
     * @param configuration the model to install markers on
     * @param severity the level of severity
     * @param attributeName
     * @param index
     * @param message
     */
    public static void installModelProblemMarker(ILaunchConfiguration configuration, final int severityError,
            final String attributeName, final int attributeIndex, final Region errorRegion, final String message)
    {
        Assert.isNotNull(configuration);
        Assert.isTrue(configuration.exists());

        try
        {
            // create an empty marker
            IMarker marker = configuration.getFile().createMarker(TLC_MODEL_ERROR_MARKER);
            // Once we have a marker object, we can set its attributes
            marker.setAttribute(IMarker.SEVERITY, severityError);
            marker.setAttribute(IMarker.MESSAGE, message);
            marker.setAttribute(TLC_MODEL_ERROR_MARKER_ATTRIBUTE_NAME, attributeName);
            marker.setAttribute(TLC_MODEL_ERROR_MARKER_ATTRIBUTE_IDX, attributeIndex);
            marker.setAttribute(IMarker.LOCATION, "");
            marker.setAttribute(IMarker.CHAR_START, errorRegion.getOffset());
            marker.setAttribute(IMarker.CHAR_END, errorRegion.getOffset() + errorRegion.getLength());

            TLCActivator.logDebug("Marker on " + attributeName
                    + ((attributeIndex != -1) ? " index: " + attributeIndex : "") + " at " + errorRegion + " "
                    + message);

        } catch (CoreException e)
        {
            TLCActivator.logError("Error installing a model marker", e);
        }
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
            IMarker[] foundMarkers = resource.findMarkers(TLC_MODEL_ERROR_MARKER, false, IResource.DEPTH_ZERO);
            return foundMarkers;
        }

        return new IMarker[0];
    }

    /**
     * Checks whether the checkpoint files exist for a given model 
     * @param launchConfig
     * @return the array of checkpoint directories, sorted from last to first
     */
    public static IResource[] getCheckpoints(ILaunchConfiguration config) throws CoreException
    {
        // yy-MM-dd-HH-mm-ss
        Pattern pattern = Pattern.compile("[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}");

        Vector checkpoints = new Vector();
        IFolder directory = getModelTargetDirectory(config);
        if (directory != null && directory.exists())
        {
            IResource[] members = directory.members();
            for (int i = 0; i < members.length; i++)
            {
                if (members[i].getType() == IResource.FOLDER)
                {
                    Matcher matcher = pattern.matcher(members[i].getName());
                    if (matcher.matches())
                    {
                        if (((IFolder) members[i]).findMember(CHECKPOINT_QUEUE) != null && 
                                ((IFolder) members[i]).findMember(CHECKPOINT_VARS) != null && 
                                ((IFolder) members[i]).findMember(CHECKPOINT_STATES) != null)
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

}
