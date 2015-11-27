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

package org.lamport.tla.toolbox.tool.tlc.output;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.LineNumberReader;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.BadLocationException;
import org.lamport.tla.toolbox.tool.tlc.output.source.ITLCOutputSource;
import org.lamport.tla.toolbox.tool.tlc.output.source.TagBasedTLCOutputIncrementalParser;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

/**
 * Reads the log file and parses the content
 * 
 * @author Simon Zambrovski
 */
public class LogFileReader {
	
	private final TagBasedTLCOutputIncrementalParser parser;
	private final File logFile;

	public LogFileReader(String name, IFile aLogFile, boolean isTraceExplorerLogFile) {
		this.logFile = new File(aLogFile.getLocation().toOSString());
		this.parser = new TagBasedTLCOutputIncrementalParser(name, ITLCOutputSource.PRIO_LOW, isTraceExplorerLogFile,
				TagBasedTLCOutputIncrementalParser.Mode.BATCH, this.logFile.length());
	}

    /**
	 * Reads the contents
	 */
	public void read(final IProgressMonitor monitor) throws IOException, BadLocationException {
		BufferedReader reader = null;
		try {
			final long numberOfLines = getLineNumbers();

			// I'm looking forward to the bug report where the int cast is
			// relevant.
			monitor.beginTask("Opening logfile "+logFile.getCanonicalPath(), (int) numberOfLines);

			reader = new BufferedReader(new FileReader(logFile));
			/*
			 * When the output file is somewhat large (several hundred KB) the
			 * toolbox hangs due to the parser inefficiently handling multiple
			 * lines at once. If the entire document representing that file is
			 * passed to the parser at once. We can send in pieces of it to
			 * solve this problem.
			 * 
			 * We send in one line at a time. Note that IDocument lines are
			 * 0-based.
			 */
			for (int lineNum = 0; lineNum < numberOfLines; lineNum++) {
				if (monitor.isCanceled()) {
					this.parser.clear();
					return;
				}
				if (lineNum % 1000 == 0) {
					monitor.worked(1000);
				}
				this.parser.addLine(reader.readLine().concat("\n"));
			}
			this.parser.done();
			monitor.worked(1);
		} catch (BadLocationException e) {
			TLCUIActivator.getDefault().logError("Error positioning in the TLC log file", e);
			throw e;
		} catch (FileNotFoundException e) {
			TLCUIActivator.getDefault().logError("Error accessing the TLC log file contents", e);
			throw e;
		} catch (IOException e) {
			TLCUIActivator.getDefault().logError("Error reading the TLC log file contents", e);
			throw e;
		} finally {
			/*
			 * The document provider is not needed. Always disconnect it to
			 * avoid a memory leak.
			 * 
			 * Keeping it connected only seems to provide synchronization of the
			 * document with file changes. That is not necessary in this
			 * context.
			 */
			monitor.done();
			if (reader != null) {
				try {
					reader.close();
				} catch (IOException e) {
					TLCUIActivator.getDefault().logError("Error closing the TLC log file contents", e);
				}
			}
		}
	}

	public long getLineNumbers() throws IOException {
		final LineNumberReader reader = new LineNumberReader(new FileReader(logFile));
		reader.skip(Long.MAX_VALUE);
		final int numberOfLines = reader.getLineNumber();
		reader.close();
		return numberOfLines;
	 }

	public ITLCOutputSource getSource() {
		return this.parser.getSource();
	}

}
