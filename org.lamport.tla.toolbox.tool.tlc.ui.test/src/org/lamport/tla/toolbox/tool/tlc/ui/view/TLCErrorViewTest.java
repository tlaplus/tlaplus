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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.easymock.EasyMock;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.TreeItem;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCError;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCError.Order;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCState;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
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

		final TLCError error = new TLCError(Order.NToOne);
		errors.add(error);

		for (int i = 1; i <= 10000; i++) {
			final TLCState state = TLCState.parseState(
					i + ": <Action line 1, col 1 to line 1, col 2 of module testLargeNumberOfStates>\nx = " + i, name);
			error.addState(state);
		}

		// show all states
		TLCUIActivator.getDefault().getPreferenceStore().setValue(ITLCPreferenceConstants.I_TLC_TRACE_MAX_SHOW_ERRORS,
				Integer.MAX_VALUE);
		
		final long before = System.currentTimeMillis();
		UIHelper.runUISync(new Runnable() {
			public void run() {
				TLCErrorView.updateErrorView(provider, new ModelEditor(dummyModel), true);
			}
		});
		assertTrue(before - System.currentTimeMillis() <= 10 * 1000); // maximally ten seconds
	}
	
	private class DummyModel extends Model {

		protected DummyModel(ILaunchConfiguration launchConfig) {
			super(launchConfig);
		}
	}

	@Test
	public void testColoring() {
		UIHelper.runUISync(new Runnable() {
			public void run() {
				try {
					doTestColoring();
				} catch (CoreException e) {
					e.printStackTrace();
				}
			}
		});
	}
	
	private void doTestColoring() throws CoreException {		
		/*
		 * Create view and check that it has been created successfully.
		 */
		final TLCErrorView view = (TLCErrorView) UIHelper.openView(TLCErrorView.ID);
		final TreeViewer viewer = view.getViewer();
		Assume.assumeNotNull(viewer);
		Assume.assumeNotNull(viewer.getTree());

		/*
		 * Create dummy error trace
		 */
		final TLCError error = new TLCError();

		String str = "1: <Initial predicate>\n" +
				"/\\ sq = <<>>\n" +
				"/\\ sqn = <<{}>>\n" +
				"/\\ i = 1\n" +
				"/\\ s = {5}\n" +
				"/\\ x = (a :> 0 @@ b :> 0 @@ c :> 0)\n" +
				"/\\ y = <<0, 0, 0>>\n" +
				"/\\ z = [a |-> 0, b |-> 0, c |-> 0]";
		error.addState(TLCState.parseState(str, "testColoring"));

		str = "2: <Action line 22, col 12 to line 29, col 33 of module TraceExplorerColoring>\n" +
				"/\\ sq = <<1>>\n" +
				"/\\ sqn = <<{},{5}>>\n" +
				"/\\ i = 2\n" +
				"/\\ s = {5, 6}\n" +
				"/\\ x = (a :> 42 @@ b :> 0 @@ c :> 0)\n" +
				"/\\ y = <<42, 0, 0>>\n" +
				"/\\ z = [a |-> 42, b |-> 0, c |-> 0]";
		error.addState(TLCState.parseState(str, "testColoring"));

		str = "3: <Action line 22, col 12 to line 29, col 33 of module TraceExplorerColoring>\n" +
				"/\\ sq = <<1, 2>>\n" +
				"/\\ sqn = <<{}, {5}, {5, 6}>>\n" +
				"/\\ i = 3\n" +
				"/\\ s = {5, 6, 7}\n" +
				"/\\ x = (a :> 42 @@ b :> 42 @@ c :> 0)\n" +
				"/\\ y = <<42, 42, 0>>\n" +
				"/\\ z = [a |-> 42, b |-> 42, c |-> 0]";
		error.addState(TLCState.parseState(str, "testColoring"));

		str = "4: <Action line 22, col 12 to line 29, col 33 of module TraceExplorerColoring>\n" +
				"/\\ sq = <<1, 2, 3>>\n" +
				"/\\ sqn = <<{}, {5}, {5, 6}, {5, 6, 7}>>\n" +
				"/\\ i = 4\n" +
				"/\\ s = {5, 6, 7, 8}\n" +
				"/\\ x = (a :> 42 @@ b :> 42 @@ c :> 42)\n" +
				"/\\ y = <<42, 42, 42>>\n" +
				"/\\ z = [a |-> 42, b |-> 42, c |-> 42]";
		error.addState(TLCState.parseState(str, "testColoring"));

		str = "5: <Action line 30, col 12 to line 37, col 29 of module TraceExplorerColoring>\n" +
				"/\\ sq = <<2, 3>>\n" +
				"/\\ sqn = <<{5}, {5, 6}, {5, 6, 7}>>\n" +
				"/\\ i = 5\n" +
				"/\\ s = {}\n" +
				"/\\ x = (a :> 42 @@ b :> 42 @@ c :> 42)\n" +
				"/\\ y = <<42, 42, 42>>\n" +
				"/\\ z = [a |-> 42, b |-> 42, c |-> 42]";
		error.addState(TLCState.parseState(str, "testColoring"));
		
		/*
		 * Feed error trace to view.
		 */
		view.setTraceInput(error, true);
		
		/*
		 * Expand all items to force coloring (expect test to fail otherwise).
		 */
		viewer.setAutoExpandLevel(TreeViewer.ALL_LEVELS);
		viewer.expandAll();

		/*
		 * Bring unordered list of treeitems into the actual error trace order.
		 */
		final Map<Integer, TreeItem> items = new HashMap<Integer, TreeItem>();
		final TreeItem[] anItems = viewer.getTree().getItems();
		for (int i = 0; i < anItems.length; i++) {
			final TreeItem item = anItems[i];
			final int idx = Integer.parseInt(item.getText(1).subSequence(13, 14).toString());
			items.put(idx, item);
		}
		
		/*
		 * Check assertions.
		 */
		assertEquals(error.getTraceSize(), items.size());
		
		// 1. state (no coloring)
		TreeItem action = items.get(1);
		assertTrue(noneOf(action.getBackground()));
		assertTrue(noneOf(action.getBackground(1)));
		
		TreeItem[] variables = action.getItems();
		assertEquals(7, variables.length);
		
		for (TreeItem variable : variables) {
			assertTrue(noneOf(variable.getBackground()));
			assertTrue(noneOf(variable.getBackground(1)));
			TreeItem[] values = variable.getItems();
			for (TreeItem value : values) {
				assertTrue(noneOf(value.getBackground()));
				assertTrue(noneOf(value.getBackground(1)));
			}
		}
		
		final Color deleted = TLCUIActivator.getDefault().getDeletedColor();
		final Color changed = TLCUIActivator.getDefault().getChangedColor();
		final Color added = TLCUIActivator.getDefault().getAddedColor();

		/*
		 * 2. state
		 */
		action = items.get(2);
		assertEquals(7, action.getItemCount());
		assertTrue(noneOf(action.getBackground()));
		assertTrue(noneOf(action.getBackground(1)));
		
		// Variable "i"
		TreeItem var = action.getItem(0);
		assertEquals(changed, var.getBackground(1));
		
		// Variable "s"
		var = action.getItem(1);
		assertEquals(changed, var.getBackground(1));
		assertEquals(2, var.getItemCount());
		assertTrue(noneOf(var.getItem(0).getBackground(1)));
		assertEquals(added, var.getItem(1).getBackground(1));
		
		// Variable "sq"
		var = action.getItem(2);
		assertEquals(changed, var.getBackground(1));
		assertEquals(1, var.getItemCount());
		assertEquals(added, var.getItem(0).getBackground(1));
		
		// Variable "sqn"
		var = action.getItem(3);
		assertEquals(changed, var.getBackground(1));
		assertEquals(2, var.getItemCount());
		assertTrue(noneOf(var.getItem(0).getBackground(1)));
		assertEquals(added, var.getItem(1).getBackground(1));
	
		// Variable "x"
		var = action.getItem(4);
		assertEquals(changed, var.getBackground(1));
		assertEquals(3, var.getItemCount());
		assertEquals(changed, var.getItem(0).getBackground(1));
		assertTrue(noneOf(var.getItem(1).getBackground(1)));
		assertTrue(noneOf(var.getItem(2).getBackground(1)));

		// Variable "y"
		var = action.getItem(5);
		assertEquals(changed, var.getBackground(1));
		assertEquals(3, var.getItemCount());
		assertEquals(changed, var.getItem(0).getBackground(1));
		assertTrue(noneOf(var.getItem(1).getBackground(1)));
		assertTrue(noneOf(var.getItem(2).getBackground(1)));
		
		// Variable "z"
		var = action.getItem(6);
		assertEquals(changed, var.getBackground(1));
		assertEquals(3, var.getItemCount());
		assertEquals(changed, var.getItem(0).getBackground(1));
		assertTrue(noneOf(var.getItem(1).getBackground(1)));
		assertTrue(noneOf(var.getItem(2).getBackground(1)));

		/*
		 * 3. state
		 */
		action = items.get(3);
		assertEquals(7, action.getItemCount());
		assertTrue(noneOf(action.getBackground()));
		assertTrue(noneOf(action.getBackground(1)));
		
		// Variable "i"
		var = action.getItem(0);
		assertEquals(changed, var.getBackground(1));
		
		// Variable "s"
		var = action.getItem(1);
		assertEquals(changed, var.getBackground(1));
		assertEquals(3, var.getItemCount());
		assertTrue(noneOf(var.getItem(0).getBackground(1)));
		assertTrue(noneOf(var.getItem(1).getBackground(1)));
		assertEquals(added, var.getItem(2).getBackground(1));
		
		// Variable "sq"
		var = action.getItem(2);
		assertEquals(changed, var.getBackground(1));
		assertEquals(2, var.getItemCount());
		assertTrue(noneOf(var.getItem(0).getBackground(1)));
		assertEquals(added, var.getItem(1).getBackground(1));
		
		// Variable "sqn"
		var = action.getItem(3);
		assertEquals(changed, var.getBackground(1));
		assertEquals(3, var.getItemCount());
		assertTrue(noneOf(var.getItem(0).getBackground(1)));
		assertTrue(noneOf(var.getItem(1).getBackground(1)));
		assertEquals(added, var.getItem(2).getBackground(1));
	
		// Variable "x"
		var = action.getItem(4);
		assertEquals(changed, var.getBackground(1));
		assertEquals(3, var.getItemCount());
		assertTrue(noneOf(var.getItem(0).getBackground(1)));
		assertEquals(changed, var.getItem(1).getBackground(1));
		assertTrue(noneOf(var.getItem(2).getBackground(1)));

		// Variable "y"
		var = action.getItem(5);
		assertEquals(changed, var.getBackground(1));
		assertEquals(3, var.getItemCount());
		assertTrue(noneOf(var.getItem(0).getBackground(1)));
		assertEquals(changed, var.getItem(1).getBackground(1));
		assertTrue(noneOf(var.getItem(2).getBackground(1)));
		
		// Variable "z"
		var = action.getItem(6);
		assertEquals(changed, var.getBackground(1));
		assertEquals(3, var.getItemCount());
		assertTrue(noneOf(var.getItem(0).getBackground(1)));
		assertEquals(changed, var.getItem(1).getBackground(1));
		assertTrue(noneOf(var.getItem(2).getBackground(1)));

		/*
		 * 4. state
		 */
		action = items.get(4);
		assertEquals(7, action.getItemCount());
		assertTrue(noneOf(action.getBackground()));
		assertTrue(noneOf(action.getBackground(1)));
		
		// Variable "i"
		var = action.getItem(0);
		assertEquals(changed, var.getBackground(1));
		
		// Variable "s"
		var = action.getItem(1);
		assertEquals(changed, var.getBackground(1));
		assertEquals(4, var.getItemCount());
		assertEquals(deleted, var.getItem(0).getBackground(1));
		assertEquals(deleted, var.getItem(1).getBackground(1));
		assertEquals(deleted, var.getItem(2).getBackground(1));
		assertEquals(added, var.getItem(3).getBackground(1));
		
		// Variable "sq"
		var = action.getItem(2);
		assertEquals(changed, var.getBackground(1));
		assertEquals(3, var.getItemCount());
		assertEquals(deleted, var.getItem(0).getBackground(1));
		assertTrue(noneOf(var.getItem(1).getBackground(1)));
		assertEquals(added, var.getItem(2).getBackground(1));
		
		// Variable "sqn"
		var = action.getItem(3);
		assertEquals(changed, var.getBackground(1));
		assertEquals(4, var.getItemCount());
		assertEquals(deleted, var.getItem(0).getBackground(1));
		assertTrue(noneOf(var.getItem(1).getBackground(1)));
		assertTrue(noneOf(var.getItem(2).getBackground(1)));
		assertEquals(added, var.getItem(3).getBackground(1));
	
		// Variable "x"
		var = action.getItem(4);
		assertEquals(changed, var.getBackground(1));
		assertEquals(3, var.getItemCount());
		assertTrue(noneOf(var.getItem(0).getBackground(1)));
		assertTrue(noneOf(var.getItem(1).getBackground(1)));
		assertEquals(changed, var.getItem(2).getBackground(1));

		// Variable "y"
		var = action.getItem(5);
		assertEquals(changed, var.getBackground(1));
		assertEquals(3, var.getItemCount());
		assertTrue(noneOf(var.getItem(0).getBackground(1)));
		assertTrue(noneOf(var.getItem(1).getBackground(1)));
		assertEquals(changed, var.getItem(2).getBackground(1));
		
		// Variable "z"
		var = action.getItem(6);
		assertEquals(changed, var.getBackground(1));
		assertEquals(3, var.getItemCount());
		assertTrue(noneOf(var.getItem(0).getBackground(1)));
		assertTrue(noneOf(var.getItem(1).getBackground(1)));
		assertEquals(changed, var.getItem(2).getBackground(1));
		
		/*
		 * Final state
		 */
		action = items.get(5);
		assertEquals(7, action.getItemCount());
		assertTrue(noneOf(action.getBackground()));
		assertTrue(noneOf(action.getBackground(1)));
		
		// Variable "i"
		var = action.getItem(0);
		assertEquals(changed, var.getBackground(1));
		
		// Variable "s"
		var = action.getItem(1);
		assertEquals(changed, var.getBackground(1));
		assertEquals(0, var.getItemCount());
		
		// Variable "sq"
		var = action.getItem(2);
		assertEquals(changed, var.getBackground(1));
		assertEquals(2, var.getItemCount());
		assertTrue(noneOf(var.getItem(0).getBackground(1)));
		assertTrue(noneOf(var.getItem(1).getBackground(1)));
		
		// Variable "sqn"
		var = action.getItem(3);
		assertEquals(changed, var.getBackground(1));
		assertEquals(3, var.getItemCount());
		assertTrue(noneOf(var.getItem(0).getBackground(1)));
		assertTrue(noneOf(var.getItem(1).getBackground(1)));
		assertTrue(noneOf(var.getItem(2).getBackground(1)));
	
		// Variable "x"
		var = action.getItem(4);
		assertTrue(noneOf(var.getBackground(1)));
		assertEquals(3, var.getItemCount());
		assertTrue(noneOf(var.getItem(0).getBackground(1)));
		assertTrue(noneOf(var.getItem(1).getBackground(1)));
		assertTrue(noneOf(var.getItem(2).getBackground(1)));

		// Variable "y"
		var = action.getItem(5);
		assertTrue(noneOf(var.getBackground(1)));
		assertEquals(3, var.getItemCount());
		assertTrue(noneOf(var.getItem(0).getBackground(1)));
		assertTrue(noneOf(var.getItem(1).getBackground(1)));
		assertTrue(noneOf(var.getItem(2).getBackground(1)));
		
		// Variable "z"
		var = action.getItem(6);
		assertTrue(noneOf(var.getBackground(1)));
		assertEquals(3, var.getItemCount());
		assertTrue(noneOf(var.getItem(0).getBackground(1)));
		assertTrue(noneOf(var.getItem(1).getBackground(1)));
		assertTrue(noneOf(var.getItem(2).getBackground(1)));
	}
	
	private boolean noneOf(Color c) {
		if (c.equals(TLCUIActivator.getDefault().getDeletedColor())) {
			return false;
		}
		if (c.equals(TLCUIActivator.getDefault().getChangedColor())) {
			return false;
		}
		if (c.equals(TLCUIActivator.getDefault().getAddedColor())) {
			return false;
		}
		return true;
	}
}
