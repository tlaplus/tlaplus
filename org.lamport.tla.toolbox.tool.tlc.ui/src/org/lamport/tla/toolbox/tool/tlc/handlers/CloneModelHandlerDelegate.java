/*******************************************************************************
 *
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Simon Zambrovski - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.model.TLCModelFactory;
import org.lamport.tla.toolbox.tool.tlc.model.TLCSpec;
import org.lamport.tla.toolbox.tool.tlc.util.ModelNameValidator;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Copies the contents of a model into a new model.
 * 
 * @author Simon Zambrovski
 */
public class CloneModelHandlerDelegate extends AbstractHandler implements IHandler {

	public static final String COMMAND_ID = "toolbox.tool.tlc.commands.model.clone.delegate";

	/**
	 * Parameter giving the name of the model to be cloned.
	 * 
	 * If this parameter is set, the call to event.getParameter(PARAM_MODEL)
	 * should return an object of type String. This is an optional parameter, so
	 * if it is not set this handler looks for the current selection to find the
	 * model to be cloned.
	 * 
	 * The model name can be of the form specName___modelName or just of the
	 * form modelName.
	 */
	public static final String PARAM_MODEL_NAME = "toolbox.tool.tlc.commands.model.clone.param.modelName";

	/**
	 * If the cloning is being done on a foreign spec, this value must be set.
	 * 
	 * N.B The Eclipse codebase is such an exceedingly well written thing that if this parameter is not defined
	 *		in the command XML, Eclipse will silently discard all contribution items containing parameters with
	 *		this value. Kwality!
	 */
	public static final String PARAM_FOREIGN_FULLY_QUALIFIED_MODEL_NAME
								= "toolbox.tool.tlc.commands.model.clone.param.foreignFullyQualifiedModelName";
	
	
	/**
	 * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
	 */
	public Object execute(ExecutionEvent event) throws ExecutionException {
		final TLCSpec spec = ToolboxHandle.getCurrentSpec().getAdapter(TLCSpec.class);
		
		Model model = null;
		/*
		 * First try to get the model from the parameters. It is an optional
		 * parameter, so it may not have been set.
		 */
		final String paramModelName = (String) event.getParameter(PARAM_MODEL_NAME);
		final String paramForeignModelName = (String) event.getParameter(PARAM_FOREIGN_FULLY_QUALIFIED_MODEL_NAME);
		final boolean isForeignClone = (paramForeignModelName != null);
		if (paramModelName != null) {
			// The name is given which means the user clicked the main menu
			// instead of the spec explorer. Under the constraint that only ever
			// a single spec can be open, lookup the current spec to eventually
			// get the corresponding model.
			model = spec.getModel(paramModelName);
		} else if (isForeignClone) {
			model = TLCModelFactory.getByName(paramForeignModelName);
		} else {
			/*
			 * No parameter try to get it from active navigator if any
			 */
			final ISelection selection = HandlerUtil.getCurrentSelectionChecked(event);
			if (selection != null && selection instanceof IStructuredSelection) {
				// model
				model = (Model) ((IStructuredSelection) selection).getFirstElement();
			}
		}

		if (model != null) {
			final InputDialog dialog = new InputDialog(UIHelper.getShellProvider().getShell(), "Clone model...",
					"Please input the new name of the model", spec.getModelNameSuggestion(model), new ModelNameValidator(spec));
			dialog.setBlockOnOpen(true);
			if (dialog.open() == Window.OK) {
				final String chosenName = dialog.getValue();

				if (isForeignClone) {
					if (model.copyIntoForeignSpec(spec, chosenName) == null) {
						throw new ExecutionException("Failed to copy with name " + chosenName
														+ " from model " + model.getName() + " in spec " + model.getSpec().getName());
					}
				} else {
					if (model.copy(chosenName) == null) {
						throw new ExecutionException("Failed to copy with name " + chosenName + " from model " + model.getName());
					}
				}

				// Open the previously created model
				final Map<String, String> parameters = new HashMap<String, String>();
				parameters.put(OpenModelHandler.PARAM_MODEL_NAME, chosenName);
				UIHelper.runCommand(OpenModelHandler.COMMAND_ID, parameters);
			}
		}
		return null;
	}
}
