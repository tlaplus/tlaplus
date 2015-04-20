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

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

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
	public void testCreateSpecStoreRelativePath() throws IOException {
		// Create...
		final File tempFile = File.createTempFile("TestSpecName", ".tla");
		final Spec spec = Spec.createNewSpec("TestSpecName", tempFile.getAbsolutePath(), false, new NullProgressMonitor());

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
}
