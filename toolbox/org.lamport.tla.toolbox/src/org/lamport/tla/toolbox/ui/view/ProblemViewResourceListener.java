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
package org.lamport.tla.toolbox.ui.view;

import org.eclipse.core.resources.IMarkerDelta;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.lamport.tla.toolbox.lifecycle.ToolboxLifecycleParticipant;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/*
 * Use an inner class because instantiation of ProblemView itself should be
 * left to the Eclipse foundation and not be triggered directly via new.
 */
public class ProblemViewResourceListener extends ToolboxLifecycleParticipant implements IResourceChangeListener {

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.lifecycle.ToolboxLifecycleParticipant#postWorkbenchWindowOpen()
	 */
	public void postWorkbenchWindowOpen() {
		// Check if there have been any markers set already
		showOrHideProblemView();
		
		// ...and listen for new markers
		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
		workspace.addResourceChangeListener(this, IResourceChangeEvent.POST_BUILD);
	}

	private void showOrHideProblemView() {
        boolean showProblems = PreferenceStoreHelper.getInstancePreferenceStore().getBoolean(
                IPreferenceConstants.I_PARSER_POPUP_ERRORS);
		if (showProblems) {
			if (TLAMarkerHelper.currentSpecHasProblems()) {
				// This used to be in Activator. However,
				// at startup there might not be an
				// activePage which results in a
				// NullPointerException. Thus, have the
				// ProblemView check the parse status when
				// UI startup complete.
				ProblemView view = (ProblemView) UIHelper.getActivePage().findView(ProblemView.ID);
				// show
				if (view != null) {
					// already shown, hide
					UIHelper.hideView(ProblemView.ID);
				}

				// not shown, show
				UIHelper.openViewNoFocus(ProblemView.ID);
			} else {
				// hide
				UIHelper.hideView(ProblemView.ID);
			}
		}
	}

	private boolean hasMarkerDelta(IResourceChangeEvent event) {
		IMarkerDelta[] deltas = event.findMarkerDeltas(TLAMarkerHelper.TOOLBOX_MARKERS_ALL_MARKER_ID, true);
		if (deltas.length > 0) {
			return true;
		}
		return false;
	}

	public void resourceChanged(IResourceChangeEvent event) {
		// no marker update
		if (!hasMarkerDelta(event)) {
			return;
		} else {
			UIHelper.runUIAsync(new Runnable() {
				public void run() {
					showOrHideProblemView();
				}
			});
		}
	}
}