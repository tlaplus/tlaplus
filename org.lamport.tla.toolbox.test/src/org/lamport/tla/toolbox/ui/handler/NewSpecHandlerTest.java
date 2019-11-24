/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
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

import java.io.IOException;
import java.nio.file.Files;
import java.util.concurrent.CountDownLatch;

import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.JobChangeAdapter;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.ui.handler.NewSpecHandler.NewSpecHandlerJob;

import junit.framework.TestCase;
import util.TLAConstants;

public class NewSpecHandlerTest extends TestCase {

	public void testNewSpecHandlerSuccess() throws InterruptedException, IOException {
		assertTrue(runJob("TestNewSpecHandlerSuccess").isOK());
		
		// Do some cleanup, leftovers seem to interfere with other tests.
		final Spec spec = Activator.getSpecManager().getSpecByName("TestNewSpecHandlerSuccess");
		Activator.getSpecManager().removeSpec(spec, new NullProgressMonitor(), true);
		assertNull(Activator.getSpecManager().getSpecByName("TestNewSpecHandlerSuccess"));
	}

	public void testNewSpecHandlerFail() throws InterruptedException, IOException, CoreException {
		// Create a project (not a specification) that is going to be in the way
		// of the NewSpecHandler and which will make it fail.
		final IWorkspace ws = ResourcesPlugin.getWorkspace();
		ws.getRoot().getProject("TestNewSpecHandlerFail").create(new NullProgressMonitor());
		assertTrue(ws.getRoot().getProject("TestNewSpecHandlerFail").exists());

		// Above only creates a project but not a spec. 
		assertNull(Activator.getSpecManager().getSpecByName("TestNewSpecHandlerFail"));

		// Try to create a spec the Toolbox way which is supposed to fail.
		final IStatus iStatus = runJob("TestNewSpecHandlerFail");
		assertEquals(Status.ERROR, iStatus.getSeverity());
		
		// As a result of the above failed attempt to create a spec
		// 'TestNewSpecHandlerFail', a spec should appear in the SpecManager
		// with a file named "Delete me".
		final Spec spec = Activator.getSpecManager().getSpecByName("TestNewSpecHandlerFail");
		assertEquals("Failed to find 'Delete me' spec in ToolboxExplorer", "Delete me", spec.getRootFile().getName());
		
		// Verify that this spec can be deleted and is gone afterwards
		// (including the dangling project this is all about).
		Activator.getSpecManager().removeSpec(spec, new NullProgressMonitor(), true);
		assertNull(Activator.getSpecManager().getSpecByName("TestNewSpecHandlerFail"));
		assertFalse(ws.getRoot().getProject("TestNewSpecHandlerFail").exists());
	}

	private IStatus runJob(String specName) throws IOException, InterruptedException {
		final NewSpecHandlerJob job = new NewSpecHandlerJob(specName,
				Files.createTempFile(specName, TLAConstants.Files.TLA_EXTENSION).toFile().getAbsolutePath(), false);
		MyJobChangeAdapter listener = new MyJobChangeAdapter();
		job.addJobChangeListener(listener);
		job.schedule();

		listener.await();

		assertNotNull(listener.getOuterEvent());
		return listener.getOuterEvent();
	}

	private static class MyJobChangeAdapter extends JobChangeAdapter {

		private IStatus outerEvent;

		private final CountDownLatch cdl;

		public MyJobChangeAdapter() {
			cdl = new CountDownLatch(1);
		}

		public void await() throws InterruptedException {
			cdl.await();
		}

		/**
		 * @return the outerEvent
		 */
		public IStatus getOuterEvent() {
			return outerEvent;
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see
		 * org.eclipse.core.runtime.jobs.JobChangeAdapter#done(org.eclipse.core.
		 * runtime.jobs.IJobChangeEvent)
		 */
		@Override
		public void done(final IJobChangeEvent event) {
			super.done(event);
			outerEvent = event.getResult();
			cdl.countDown();
		}
	}
}
