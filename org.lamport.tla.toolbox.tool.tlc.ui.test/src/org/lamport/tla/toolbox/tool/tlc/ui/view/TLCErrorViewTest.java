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

package org.lamport.tla.toolbox.tool.tlc.ui.view;

import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.easymock.EasyMock;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.junit.Ignore;
import org.junit.Test;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCError;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCState;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.preference.ITLCPreferenceConstants;
import org.lamport.tla.toolbox.util.UIHelper;

public class TLCErrorViewTest  {

	@SuppressWarnings("unchecked")
	@Test//(timeout=10000) // 10 seconds timeout (should be sufficient even on old machines)
	@Ignore
	public void testLargeNumberOfStates() throws CoreException {
		final String name = "testLargeNumberOfStates";

		final IPath path = EasyMock.createNiceMock(IPath.class);
		EasyMock.expect(path.removeFileExtension()).andReturn(path).anyTimes();
		EasyMock.expect(path.lastSegment()).andReturn(name).anyTimes();
		EasyMock.replay(path);

		final IProject project = EasyMock.createNiceMock(IProject.class);
		EasyMock.expect(project.getName()).andReturn(name).anyTimes();
		EasyMock.replay(project);

		final IFile file = EasyMock.createNiceMock(IFile.class);
		EasyMock.expect(file.findMarkers((String) EasyMock.anyObject(), EasyMock.anyBoolean(), EasyMock.anyInt()))
				.andReturn(new IMarker[0]);
		EasyMock.expect(file.getName()).andReturn(name).anyTimes();
		EasyMock.expect(file.getLocation()).andReturn(path).anyTimes();
		EasyMock.expect(file.getProject()).andReturn(project).anyTimes();
		EasyMock.replay(file);

		final ILaunchConfiguration launchConfig = EasyMock.createNiceMock(ILaunchConfiguration.class);
		EasyMock.expect(launchConfig.getFile()).andReturn(file).anyTimes();
		EasyMock.expect(launchConfig.isWorkingCopy()).andReturn(false).anyTimes();
		EasyMock.expect(launchConfig.getAttribute((String) EasyMock.anyObject(), (List<String>) EasyMock.anyObject()))
				.andReturn(new ArrayList<String>()).anyTimes();
		EasyMock.replay(launchConfig);

		final Model dummyModel = new DummyModel(launchConfig);
		// Cannot be mocked because it's not an interface.
		final TLCModelLaunchDataProvider provider = new TLCModelLaunchDataProvider(dummyModel);
		final List<TLCError> errors = new ArrayList<TLCError>();
		provider.setErrors(errors);

		final TLCError error = new TLCError();
		errors.add(error);

		for (int i = 1; i <= 10000; i++) {
			final TLCState state = TLCState.parseState(
					i + ": <Action line 1, col 1 to line 1, col 2 of module testLargeNumberOfStates>\nx = " + i, name);
			error.addState(state, true);
		}

		// show all states
		TLCUIActivator.getDefault().getPreferenceStore().setValue(ITLCPreferenceConstants.I_TLC_TRACE_MAX_SHOW_ERRORS,
				Integer.MAX_VALUE);
		
		final long before = System.currentTimeMillis();
		UIHelper.runUISync(new Runnable() {
			public void run() {
				TLCErrorView.updateErrorView(provider, dummyModel, true);
			}
		});
		assertTrue(before - System.currentTimeMillis() <= 10 * 1000); // maximally ten seconds
	}
	
	private class DummyModel extends Model {

		protected DummyModel(ILaunchConfiguration launchConfig) {
			super(launchConfig);
		}
	}
}
