/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
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
package org.lamport.tla.toolbox.tool.tlc.model;

import java.io.IOException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.ui.PlatformUI;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tlc2.output.SpecTraceExpressionWriter;

public class TraceExpressionModelWriter extends SpecTraceExpressionWriter {
    /**
     * {@inheritDoc}
     */
	@Override
    protected String getTLAModuleClosingTag() {
        final StringBuilder sb = ResourceHelper.getModuleClosingTag();
    	
    	return sb.toString();
    }
	
    /**
     * Write the content to files
     * @param tlaFile
     * @param cfgFile
     * @param monitor
     * @throws CoreException
     */
	public void writeFiles(final IFile tlaFile, final IFile cfgFile, final IProgressMonitor monitor) throws CoreException {
		final ContentWriter cw = (inputStream, forTLAFile) -> {
			final IFile file = forTLAFile ? tlaFile : cfgFile;
			
			if (file.exists()) {
				try {
					file.setContents(inputStream, IResource.FORCE, monitor);
				} catch (final CoreException ce) {
					throw new IOException("Exception writing file " + ce.getMessage(), ce);
				}
			} else {
				throw new IOException("Expected file " + file.getName() + " has been removed externally.");
			}
		};
		
		try {
			super.writeFiles(cw);
		} catch (final IOException e) {
			throw new CoreException(new Status(IStatus.ERROR, PlatformUI.PLUGIN_ID, IStatus.ERROR,
									"Exception encountered attempting to write modules for the model checking.", e));
		}
    }
}
