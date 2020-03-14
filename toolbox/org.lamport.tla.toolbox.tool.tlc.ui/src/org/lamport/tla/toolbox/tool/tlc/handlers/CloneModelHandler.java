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
 *   Simon Zambrowski - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.tool.tlc.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.model.Model;

/**
 * Clones the launch configuration
 */
public class CloneModelHandler extends AbstractHandler implements IModelConfigurationConstants {
	
	public static final String PARAM_MODEL_NAME = "toolbox.tool.tlc.commands.model.open.param.modelName";
	public static final String PARAM_MODELCOPY_NAME = "toolbox.tool.tlc.commands.model.open.param.modelCloneName";
	public static final String COMMAND_ID = "toolbox.tool.tlc.commands.model.clone";

	public Object execute(final ExecutionEvent event) throws ExecutionException {
		final String fullQualifiedModelName = event.getParameter(PARAM_MODEL_NAME);
		final String modelCopyName = event.getParameter(PARAM_MODELCOPY_NAME);
		if (fullQualifiedModelName == null) {
			return null;
		}

		final Model model = Model.getByName(fullQualifiedModelName);
		if (model == null) {
			throw new ExecutionException("Failed to find model by name " + fullQualifiedModelName);
		}
		
		if (model.copy(modelCopyName) == null) {
			throw new ExecutionException(
					"Failed to create copy with name " + modelCopyName + " of model " + model.getName());
		}
		return null;
	}
}
