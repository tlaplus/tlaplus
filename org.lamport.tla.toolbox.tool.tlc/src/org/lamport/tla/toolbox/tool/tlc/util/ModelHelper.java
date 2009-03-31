package org.lamport.tla.toolbox.tool.tlc.util;

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
    public static IFile getConfigFile(IResource rootModule)
    {

        IPath cfgPath = rootModule.getLocation().removeFileExtension().addFileExtension("cfg");

        // create config file
        IWorkspaceRunnable configCreateJob = new ConfigCreationOperation(cfgPath);
        // create it
        try
        {
            ResourcesPlugin.getWorkspace().run(configCreateJob, null);
        } catch (CoreException e)
        {
            e.printStackTrace();
            // exception, no chance to recover
        }

        IFile cfgFile = ResourceHelper.getLinkedFile(rootModule.getProject(), cfgPath.toOSString(), true);

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
     * Creates a serial version of the assignment list
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
            buffer.append(assign.getLabel()).append(LIST_DELIMITER);
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
            if (assign.getRight() != null)
            {
                buffer.append(assign.getRight());
            }

            result.add(buffer.toString());
        }
        return result;
    }

    /**
     * De-serialize assignment list
     * @param serializedList
     * @return
     */
    public static List deserializeAssignmentList(List serializedList)
    {
        Vector result = new Vector(serializedList.size());
        Iterator iter = serializedList.iterator();
        String[] fields = new String[] { null, "", "" };
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
            Assignment assign = new Assignment(fields[0], params, fields[2]);
            result.add(assign);
        }
        return result;
    }

    /**
     * De-serialize formula list, to a list of formulas, that are selected (have a leading "1")
     * @param serializedList
     * @return a list of formulas
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

        buffer.append(identifier).append(" ==\n");

        if (config.getAttribute(MODEL_BEHAVIOR_IS_CLOSED_SPEC_USED, MODEL_BEHAVIOR_IS_CLOSED_SPEC_USED_DEFAULT))
        {
            buffer.append(config.getAttribute(MODEL_BEHAVIOR_CLOSED_SPECIFICATION, EMPTY_STRING));
        } else
        {
            String modelInit = config.getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT, EMPTY_STRING);
            String modelNext = config.getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT, EMPTY_STRING);
            String modelFairness = config.getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_FAIRNESS, EMPTY_STRING);

            buffer.append(modelInit).append(" /\\[][ ").append(modelNext).append(" ]_")
            // TODO replace vars
                    .append("vars").append(" /\\ ").append(modelFairness);
        }
        return new String[] { identifier, buffer.toString() };
    }

    /**
     * Create representation of constants
     * @param config launch configuration
     * @return a list of string pairs each representing a constant instantiation 
     * @throws CoreException 
     */
    public static List createConstantsContent(ILaunchConfiguration config) throws CoreException
    {
        List constants = ModelHelper.deserializeAssignmentList(config.getAttribute(MODEL_PARAMETER_CONSTANTS,
                new Vector()));
        Vector constantContent = new Vector(constants.size());

        Assignment constant;
        String[] content;
        String label;
        for (int i = 0; i < constants.size(); i++)
        {
            label = getValidIdentifier("const");
            constant = (Assignment) constants.get(i);
            content = new String[] { constant.getLabel() + " <- " + label,
                    constant.getParametrizedLabel(label) + " ==\n" + constant.getRight() };
            constantContent.add(content);
        }
        return constantContent;
    }

    /**
     * Converts formula list to a string representation
     * @param serializedFormulaList
     * @param labelingScheme
     * @return
     */
    public static List createListContent(List serializedFormulaList, String labelingScheme) 
    {
        List formulaList = ModelHelper.deserializeFormulaList(serializedFormulaList);
        Vector resultContent = new Vector(formulaList.size());
        String[] content;
        String label;
        for (int i = 0; i < formulaList.size(); i++)
        {
            label = getValidIdentifier(labelingScheme);
            content = new String[]{label, label + " ==\n" + ((Formula)formulaList.get(i)).getFormula()};
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
            Thread.sleep(1000);
        } catch (InterruptedException e)
        {
        }
        return schema + "_" + System.currentTimeMillis();
    }

}
