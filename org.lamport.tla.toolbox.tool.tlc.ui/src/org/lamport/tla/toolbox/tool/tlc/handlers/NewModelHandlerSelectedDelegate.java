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
 *   Simon Zambrovski - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.ISelectionService;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.tlc.ui.modelexplorer.ModelContentProvider;
import org.lamport.tla.toolbox.tool.tlc.ui.modelexplorer.ModelContentProvider.Group;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Delegates the model creation for the spec selected from the toolbox explorer
 */
public class NewModelHandlerSelectedDelegate extends AbstractHandler implements IHandler
{
	/* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
	public Object execute(ExecutionEvent event) throws ExecutionException {
		/*
		 * Try to get the spec from active navigator if any
		 */
		final ISelection selection = HandlerUtil.getCurrentSelectionChecked(event);
		if (selection != null && selection instanceof IStructuredSelection
				&& ((IStructuredSelection) selection).size() == 1) {
			Object selected = ((IStructuredSelection) selection).getFirstElement();
			if (selected instanceof ModelContentProvider.Group) {
				// Convert the group to its corresponding spec
				selected = ((Group) selected).getSpec();
			}

			if (selected instanceof Spec) {
				final Map<String, String> parameters = new HashMap<String, String>();
				// fill the spec name for the handler
				parameters.put(NewModelHandler.PARAM_SPEC_NAME, ((Spec) selected).getName());
				// delegate the call to the new model handler
				UIHelper.runCommand(NewModelHandler.COMMAND_ID, parameters);
			}
		}
		return null;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#isEnabled()
	 */
	public boolean isEnabled() {
		final ISelection selection = getSelection();
		if (selection instanceof IStructuredSelection) {
			final IStructuredSelection iss = (IStructuredSelection) selection;
			final Object selected = iss.getFirstElement();
			if (selected instanceof Spec && ((Spec) selected).isCurrentSpec()) {
				return true;
			} else if (selected instanceof ModelContentProvider.Group) {
				final ModelContentProvider.Group group = (Group) selected;
				return group.getSpec().isCurrentSpec();
			}
		}
		return false;
	}
	
	private static ISelection getSelection() {
		try {
			IWorkbenchWindow ww = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
			if (ww != null) {
				ISelectionService service = ww.getSelectionService();
				if (service != null) {
					return service.getSelection();
				}
			}
		} catch(IllegalStateException e) {
			return null;
		}
		return null;
	}
}
