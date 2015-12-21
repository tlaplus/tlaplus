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
package org.lamport.tla.toolbox.ui.navigator;

import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.viewers.AbstractTreeViewer;
import org.eclipse.ui.navigator.CommonViewer;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.lifecycle.ToolboxLifecycleParticipant;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.UIHelper;

public class ToolboxExplorerResourceListener extends ToolboxLifecycleParticipant implements IResourceChangeListener {

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.lifecycle.ToolboxLifecycleParticipant#postWorkbenchWindowOpen()
	 */
	public void postWorkbenchWindowOpen() {
		// We might have missed events during Toolbox startup when there was
		// a workspace but no UI yet.
		resourceChanged(null);
		
		// update CNF viewers
		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
		workspace.addResourceChangeListener(this);
	}
	
	public void resourceChanged(final IResourceChangeEvent event) {
		UIHelper.runUIAsync(new Runnable() {
			public void run() {
				ToolboxExplorer.refresh();
				// Expand the current spec and all its children
				final CommonViewer viewer = ToolboxExplorer.getViewer();
				// Event is only null when this Ctor calls us causing the
				// initial expanded state of a spec to be fully expanded.
				// Afterwards, the users expanded states is preserved.
				if (event == null && viewer != null) { // viewer might already be disposed which happens when the Toolbox shuts down.
					final Spec specLoaded = Activator.getSpecManager().getSpecLoaded();
					viewer.expandToLevel(specLoaded,
							AbstractTreeViewer.ALL_LEVELS);
				}
			}
		});
	}
}