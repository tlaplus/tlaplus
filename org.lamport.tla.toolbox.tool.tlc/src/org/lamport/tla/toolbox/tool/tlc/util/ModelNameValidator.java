/**
 * 
 */
package org.lamport.tla.toolbox.tool.tlc.util;

import org.eclipse.core.resources.IProject;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.dialogs.IInputValidator;

public class ModelNameValidator implements IInputValidator
{
    private final IProject project;

    public ModelNameValidator(IProject project)
    {
        this.project = project;

    }

    public String isValid(String newText)
    {

        if (newText == null || "".equals(newText))
        {
            return "Model name must be not empty";
        }
        ILaunchConfiguration existingModel = ModelHelper.getModelByName(project, newText);
        if (existingModel != null)
        {
            return "Model with the name " + newText + " already exists. Please choose a different name";
        }
        // a model name cannot start with the name of the spec + __
        // this causes a NPE in OpenModelHandler because the method
        // ModelHelper.getModelByName() will not be able to find the model
        if (newText.indexOf(project.getName()+"___") == 0)
        {
            return "Model name cannot begin with \"" + project.getName() + "___\".";
        }
        return null;
    }
}