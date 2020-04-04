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
package pcal;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.junit.Before;

import util.TLAConstants;
import util.ToolIO;

public abstract class PCalTest {
	
	@Before
	public void setup() {
		// Make tool capture the output written to ToolIO.out. Otherwise,
		// ToolIO#getAllMessages returns an empty array.
		ToolIO.setMode(ToolIO.TOOL);
		
		// Reset ToolIO for each test case. Otherwise, a test case sees the output of
		// the previous tests.
		ToolIO.reset();
	}

	protected static String writeFile(String filename, String content) throws IOException {
		final Path path = Files.createFile(Paths.get(filename + TLAConstants.Files.TLA_EXTENSION));
		Files.write(path, content.getBytes());
		
		final File file = path.toFile();
		file.deleteOnExit();
		return file.getAbsolutePath();
	}
	
	protected static String writeTempFile(String filename, String content) throws IOException {
		final Path path = Files.createTempFile(filename, TLAConstants.Files.TLA_EXTENSION);
		Files.write(path, content.getBytes());
		
		final File file = path.toFile();
		file.deleteOnExit();
		return file.getAbsolutePath();
	}
}
