package org.lamport.tla.toolbox.tool.tlc.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Opens a model configuration in the editor
 * @author Simon Zambrovski 
 * @version $Id$
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class OpenModelHandler extends AbstractHandler implements IConfigurationConstants
{
    public static final String COMMAND_ID = "toolbox.tool.tlc.commands.model.open";
    public static final String PARAM_MODEL_NAME = "toolbox.tool.tlc.commands.model.open.param";

    public static final String EDITOR_ID = "org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor";

    /**
     * The constructor.
     */
    public OpenModelHandler()
    {
    }

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        String modelName = event.getParameter((String) PARAM_MODEL_NAME);
        System.out.println("Open handler invoked on " + modelName);

        IFile launchFile = ModelHelper.getModelByName(modelName).getFile();
        UIHelper.openEditor(EDITOR_ID, launchFile);

        System.out.println("Finished open handler");

        return null;
    }
}
