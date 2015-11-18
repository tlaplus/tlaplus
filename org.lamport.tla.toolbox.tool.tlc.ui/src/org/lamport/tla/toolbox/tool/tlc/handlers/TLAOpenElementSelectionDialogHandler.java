/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 *
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
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/

package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.org.eclipse.ui.dialogs.FilteredItemsSelectionDialog;
import org.lamport.tla.toolbox.spec.Module;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.tlc.ui.dialog.TLAFilteredItemsSelectionDialog;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.ui.handler.OpenModuleHandler;
import org.lamport.tla.toolbox.ui.handler.OpenSpecHandler;
import org.lamport.tla.toolbox.util.UIHelper;

public class TLAOpenElementSelectionDialogHandler extends AbstractHandler implements IHandler {

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
	 */
	public Object execute(final ExecutionEvent event) throws ExecutionException {
		final FilteredItemsSelectionDialog dialog = new TLAFilteredItemsSelectionDialog(HandlerUtil.getActiveShell(event));
		dialog.open();
		
		final Object[] result = dialog.getResult();
		if (result != null && result.length == 1) {
			final Map<String, String> parameters = new HashMap<String, String>();
			if (result[0] instanceof Module && ((Module) result[0]).isRoot()) {
				parameters.put(OpenSpecHandler.PARAM_SPEC, ((Module) result[0]).getModuleName());
				UIHelper.runCommand(OpenSpecHandler.COMMAND_ID, parameters);
			} else if (result[0] instanceof Module) {
				parameters.put(OpenModuleHandler.PARAM_MODULE, ((Module) result[0]).getModuleName());
				UIHelper.runCommand(OpenModuleHandler.COMMAND_ID, parameters);
			} else if (result[0] instanceof ILaunchConfiguration) {
				parameters.put(OpenModelHandler.PARAM_MODEL_NAME,
						ModelHelper.getModelName(((ILaunchConfiguration) result[0]).getFile()));
				UIHelper.runCommand(OpenModelHandler.COMMAND_ID, parameters);
			} else if (result[0] instanceof Spec) {
				parameters.put(OpenSpecHandler.PARAM_SPEC, ((Spec) result[0]).getName());
				UIHelper.runCommand(OpenSpecHandler.COMMAND_ID, parameters);
			}
		}
		return null;
	}
}
