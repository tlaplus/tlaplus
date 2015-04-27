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

package org.lamport.tla.toolbox.ui.handler;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.util.HashMap;

import junit.framework.TestCase;

import org.eclipse.core.internal.resources.LinkDescription;
import org.eclipse.core.internal.resources.Project;
import org.eclipse.core.internal.resources.ProjectDescription;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.ResourceHelper;

@SuppressWarnings("restriction")
public class AddModuleHandlerTest extends TestCase {

	/*
	 * Test that a create module file is stored realtive to the project
	 * 
	 * see SpecTest if this fails because of non-matching paths.
	 */
	public void testCreateModuleStoreRelativePath() throws IOException, CoreException {
		// Need a per invocation temp directory to avoid writing to the same
		// .project file over and over again.
		final File tempDirectory = createTempDirectory();

		// Create...
		final File specFile = new File(tempDirectory + File.separator + "TestSpecName.tla");
		specFile.createNewFile();
		final Spec spec = Spec.createNewSpec("TestSpecName", specFile.getAbsolutePath(), false,
				new NullProgressMonitor());

		final AddModuleHandler addModuleHandler = new AddModuleHandler();
		final File moduleFileRaw = new File(tempDirectory + File.separator + "TestModuleName.tla");
		moduleFileRaw.createNewFile();
		final IFile moduleFile = addModuleHandler.createModuleFile(spec, "TestModuleName",
				new Path(moduleFileRaw.getAbsolutePath()));

		// ...check
		assertNotNull(moduleFile);
		assertTrue(moduleFile.isAccessible());
		assertTrue(moduleFile.isLinked());

		// could use non-internal alternative
		// project.getWorkspace().loadProjectDescription(path) instead, but then
		// need to known path to .project file
		assertTrue(spec.getProject() instanceof Project);
		final Project project = (Project) spec.getProject();
		final ProjectDescription description = project.internalGetDescription();
		final ProjectDescription pd = (ProjectDescription) description;
		final HashMap<IPath, LinkDescription> links = pd.getLinks();
		assertEquals(2, links.size()); // spec + module
		for (LinkDescription linkDescription : links.values()) {
			final URI uri = linkDescription.getLocationURI();
			assertTrue(uri.toASCIIString().startsWith(ResourceHelper.PARENT_ONE_PROJECT_LOC));
		}
	}

	private static File createTempDirectory() throws IOException {
		final File temp = File.createTempFile("temp", Long.toString(System.nanoTime()));

		if (!(temp.delete())) {
			throw new IOException("Could not delete temp file: " + temp.getAbsolutePath());
		}

		if (!(temp.mkdir())) {
			throw new IOException("Could not create temp directory: " + temp.getAbsolutePath());
		}

		return temp;
	}
}
