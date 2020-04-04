package org.lamport.tla.toolbox.tool.tlc.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.model.TLCSpec;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
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
	public static final String PARAM_EXPAND_SECTIONS = "toolbox.tool.tlc.commands.model.open.param.expand.properties";
	public static final String PARAM_EXPAND_SECTIONS_DELIM = ",";
	
	public static final String EDITOR_ID = "org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor";

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#execute(org.eclipse.core.commands.ExecutionEvent)
	 */
	public Object execute(final ExecutionEvent event) throws ExecutionException {
		// The non-qualified model name (no spec prefix)
		// The ModelHelper associates it implicitly with the current spec
		final String modelName = event.getParameter(PARAM_MODEL_NAME);

		final Model model = ToolboxHandle.getCurrentSpec().getAdapter(TLCSpec.class).getModel(modelName);
		final IFile launchFile = model.getLaunchConfiguration().getFile();

		if (!launchFile.exists()) {
			throw new ExecutionException("Model file " + launchFile.getFullPath().toOSString()
					+ " does not exist. Try restarting the Toolbox and if that does not help, delete the model from the Spec Explorer.");
		}
		
		final ModelEditor modelEditor = (ModelEditor) UIHelper.openEditor(EDITOR_ID, launchFile);
		final String expand = event.getParameter(PARAM_EXPAND_SECTIONS);
		if (expand != null) {
			modelEditor.expandSections(expand.split(PARAM_EXPAND_SECTIONS_DELIM));
		}
		
		return null;
	}
}
