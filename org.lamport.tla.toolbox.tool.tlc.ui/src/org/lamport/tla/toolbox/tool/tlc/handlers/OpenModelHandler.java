package org.lamport.tla.toolbox.tool.tlc.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Opens a model configuration in the editor
 * 
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class OpenModelHandler extends AbstractHandler implements IConfigurationConstants {
	public static final String COMMAND_ID = "toolbox.tool.tlc.commands.model.open";
	public static final String PARAM_MODEL_NAME = "toolbox.tool.tlc.commands.model.open.param";

	public static final String EDITOR_ID = "org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor";

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#execute(org.eclipse.core.commands.ExecutionEvent)
	 */
	public Object execute(final ExecutionEvent event) throws ExecutionException {
		// The non-qualified model name (no spec prefix)
		// The ModelHelper associates it implicitly with the current spec
		final String modelName = event.getParameter((String) PARAM_MODEL_NAME);
		TLCUIActivator.getDefault().logDebug("Open handler invoked on " + modelName);

		final IFile launchFile = ModelHelper.getModelByName(modelName).getFile();
		UIHelper.openEditor(EDITOR_ID, launchFile);

		TLCUIActivator.getDefault().logDebug("Finished open handler");

		return null;
	}
}
