/**
 * 
 */
package org.lamport.tla.toolbox.tool.tlc.util;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.jface.dialogs.IInputValidator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.model.TLCSpec;

public class ModelNameValidator implements IInputValidator
{
    private final Spec spec;
    
    public ModelNameValidator(Spec spec) {
    	this.spec = spec;
    }

    public String isValid(String newText)
    {

        if (newText == null || "".equals(newText))
        {
            return "Model name must be not empty";
        }
        Model existingModel = spec.getAdapter(TLCSpec.class).getModel(newText);
        if (existingModel != null)
        {
            return "Model with the name " + newText + " already exists. Please choose a different name";
        }
        // a model name cannot start with the name of the spec + __
        // this causes a NPE in OpenModelHandler because the method
        // ModelHelper.getModelByName() will not be able to find the model
        if (newText.indexOf(spec.getName()+"___") == 0)
        {
            return "Model name cannot begin with \"" + spec.getName() + "___\".";
        }
        if (newText.contains(":")) {
        	return "Model name cannot contain ':' characters.";
        }
        IStatus fileStatus = ResourcesPlugin.getWorkspace().validateName(newText, IResource.FILE);
        if (! fileStatus.isOK()) {
          return fileStatus.getMessage(); 
        }
        return null;
        
    }
}