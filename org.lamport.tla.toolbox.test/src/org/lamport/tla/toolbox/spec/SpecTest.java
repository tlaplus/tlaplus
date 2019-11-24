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

package org.lamport.tla.toolbox.spec;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.preference.IPreferenceStore;
import org.junit.Assert;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

import junit.framework.TestCase;
import util.TLAConstants;

public class SpecTest extends TestCase {

	/*
	 * Creates a new spec and checks that the path variables stored in the
	 * spec's (project's) metadata are relative. We want portable
	 * specifications.
	 * 
	 * This test fails on Mac OS X unless "-Djava.io.tmpdir=/private/tmp/" is
	 * set. See
	 * org.lamport.tla.toolbox.util.ResourceHelper.isProjectParent(IPath,
	 * IProject) for the reason why. Maven build sets this VM property.
	 */
	public void testCreateSpecStoreRelativePath() throws IOException, CoreException {
		// Create...
		final File tempFile = File.createTempFile("TestCreateSpecStoreRelativePath", TLAConstants.Files.TLA_EXTENSION);
		final Spec spec = Spec.createNewSpec("TestCreateSpecStoreRelativePath", tempFile.getAbsolutePath(), false, new NullProgressMonitor());
		
		// ...check it's correct.
		final IProject project = spec.getProject();
		final IPreferenceStore store = PreferenceStoreHelper.getProjectPreferenceStore(project);
		final String path = store.getString(IPreferenceConstants.P_PROJECT_ROOT_FILE);
		// This is the internal representation... 
		assertTrue(path.toString().startsWith(ResourceHelper.PARENT_ONE_PROJECT_LOC));
		
		// ...eExternally it's a regular file.
		final IFile rootFile = PreferenceStoreHelper.readProjectRootFile(project);
		assertTrue(rootFile.isLinked());
		assertTrue(rootFile.isAccessible());
	}
	
	/*
	 * Tries to create a new spec in a read-only directory. Expects a
	 * CoreException to be thrown. The CoreException is caught by the Toolbox UI
	 * eventually telling the user what happened.
	 * 
	 * This Test fails on Microsoft Windows because setReadOnly has not the
	 * desired effect.
	 */
	public void testCreateSpecInReadOnlyDirectory() throws IOException {
		// Create...
		final Path tempDirectory = Files.createTempDirectory("ReadOnlyDirectory" + System.currentTimeMillis());
		final File tempFile = Files
				.createTempFile(tempDirectory, "TestCreateSpecInReadOnlyDirectory", TLAConstants.Files.TLA_EXTENSION)
				.toFile();

//		Assume.assumeTrue(tempDirectory.toFile().setReadOnly());
		if (!tempDirectory.toFile().setReadOnly()) {
			// Setting the test-file to read-only doesn't appear to work on Windows.
			// Normally, this case can be handled with Assume.assumeTrue(tempDirectory...)
			// but this test runs as an Eclipse Plug-in test whose Junit runner doesn't
			// appear to correctly handle JUunit's AssumptionViolationException.
			assertTrue(Platform.OS_WIN32.equals(Platform.getOS()));
			return;
		}
		
		try {
			Spec.createNewSpec("TestCreateSpecInReadOnlyDirectory", tempFile.getAbsolutePath(), false, new NullProgressMonitor());
		} catch (CoreException e) {
			assertTrue(e.getMessage().contains("read-only"));
			return;
		} finally {
			tempDirectory.toFile().setWritable(true);
		}
		Assert.fail("Creating a spec in a read-only directory should fail with a CoreException.");
	}
	
	/*
	 * Verify that specs and the their corresponding project are deleted correctly.
	 */
	public void testCreateDeleteSpec() throws CoreException, IOException {
		createDelete("TestCreateDeleteSpec", true);
	}

	/*
	 * Verify that specs and the their corresponding project are deleted correctly with forget.
	 */
	public void testCreateDeleteSpecForget() throws CoreException, IOException {
		createDelete("TestCreateDeleteSpecForget", true);
	}

	private void createDelete(final String specName, boolean forget) throws IOException, CoreException {
		// Create...
		final File tempFile = File.createTempFile(specName, TLAConstants.Files.TLA_EXTENSION);
		final Spec spec = Spec.createNewSpec("TestCreateDeleteSpec", tempFile.getAbsolutePath(), false, new NullProgressMonitor());
		final IProject project = spec.getProject();
		
		final WorkspaceSpecManager wsm = new WorkspaceSpecManager(new NullProgressMonitor());
		wsm.removeSpec(spec, new NullProgressMonitor(), forget);
		
		// Make sure that the project has been deleted.
		assertFalse(project.exists());
		final IWorkspace ws = ResourcesPlugin.getWorkspace();
		for (final IProject aProject : ws.getRoot().getProjects()) {
			assertNotSame(project.getName(), aProject.getName());
		}
		
		Spec mostRecentlyOpenedSpec = wsm.getMostRecentlyOpenedSpec();
		assertNull(mostRecentlyOpenedSpec != null ? mostRecentlyOpenedSpec.getName() : "", mostRecentlyOpenedSpec);
	}
}
