package org.lamport.tla.toolbox.tool.tlc.util;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.core.ILaunchManager;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.job.ConfigCreationOperation;
import org.lamport.tla.toolbox.tool.tlc.job.ExtendingTLAModuleCreationOperation;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.util.ResourceHelper;

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
    private static final String LIST_DELIMITER = ";";
    private static final String PARAM_DELIMITER = ":";

    /**
     * Constructs the model called FOO_MC_1 from the SpecName FOO
     * if FOO_MC_1 already exists, delivers FOO_MC_2, and so on...
     * 
     * This method tests the existence of the launch configuration AND of the file
     * 
     * @param specProject
     * @param specName
     * @return
     */
    public static String constructModelName(IProject specProject, String specName)
    {
        return doConstructModelName(specProject, specName + "_MC_1");
    }

    /**
     * Implementation of the {@link ModelHelper#constructModelName(IProject, String)}
     * @param specProject
     * @param proposition
     * @return
     */
    private static String doConstructModelName(IProject specProject, String proposition)
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
     * Convenience method retrieving the model for the project of the current specification
     * @param modelName name of the model
     * @return launch configuration or null, if not found
     */
    public static ILaunchConfiguration getModelByName(String modelName)
    {
        return getModelByName(ToolboxHandle.getCurrentSpec().getProject(), modelName);
    }

    /**
     * @param specProject
     * @param modelName
     * @return
     */
    public static ILaunchConfiguration getModelByName(IProject specProject, String modelName)
    {
        // TODO! add project test
        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
        ILaunchConfigurationType launchConfigurationType = launchManager
                .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_ID);

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
            // TODO Auto-generated catch block
            e.printStackTrace();
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
     * Retrieves the the config file
     * REFACTOR HACK 
     */
    public static IFile getConfigFile(IResource modelRootFile, IProgressMonitor monitor)
    {

        IPath cfgPath = modelRootFile.getLocation().removeFileExtension().addFileExtension("cfg");

        // create config file
        IWorkspaceRunnable configCreateJob = new ConfigCreationOperation(cfgPath);
        // create it
        try
        {
            ResourcesPlugin.getWorkspace().run(configCreateJob, monitor);
        } catch (CoreException e)
        {
            e.printStackTrace();
            // exception, no chance to recover
        }

        IFile cfgFile = ResourceHelper.getLinkedFile(modelRootFile.getProject(), cfgPath.toOSString(), true);

        return cfgFile;
    }

    /**
     * Creates a new model root and retrieves the handle to it
     */
    public static IFile getNewModelRootFile(IResource specRootModule, String modelName)
    {
        // construct new model checking root module name
        IPath modelRootPath = specRootModule.getLocation().removeLastSegments(1).append(modelName + ".tla");

        // create a module
        IWorkspaceRunnable moduleCreateJob = new ExtendingTLAModuleCreationOperation(modelRootPath, ResourceHelper
                .getModuleName(specRootModule));
        // create it
        try
        {
            ResourcesPlugin.getWorkspace().run(moduleCreateJob, null);
        } catch (CoreException e)
        {
            e.printStackTrace();
            // exception, no chance to recover
        }

        // create a link in the project
        IFile modelRootFile = ResourceHelper.getLinkedFile(specRootModule.getProject(), modelRootPath.toOSString(),
                true);

        return modelRootFile;
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
            // TODO Auto-generated catch block
            e.printStackTrace();
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
        String constraint = config.getAttribute(propertyName, EMPTY_STRING);
        if (EMPTY_STRING.equals(constraint))
        {
            return result;
        }
        String identifier = getValidIdentifier(labelingScheme);
        StringBuffer buffer = new StringBuffer();

        // the identifier
        buffer.append(identifier).append(" ==\n");
        buffer.append(constraint);

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
     * TODO re-implement
     */
    public static String getValidIdentifier(String schema)
    {
        try
        {
            Thread.sleep(10);
        } catch (InterruptedException e)
        {
        }
        return schema + "_" + System.currentTimeMillis();
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

}
