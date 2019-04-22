/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
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
package util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;

import org.junit.Test;

public class ExecutionStatisticsCollectorTest {

	// Opt-out

	@Test
	public void testOptOutNoFile() throws IOException {
		final String tmpdir = System.getProperty("java.io.tmpdir");
		final File tempFile = new File(tmpdir + File.separator + "esc" + System.currentTimeMillis() + ".txt");
		tempFile.deleteOnExit();
		
		final ExecutionStatisticsCollector esc = new ExecutionStatisticsCollector(true, tempFile.getAbsolutePath());
		
		final String identifierA = esc.getIdentifier();
		assertNotNull(identifierA);
		assertNotNull(esc.getIdentifier());
		assertEquals(identifierA, esc.getIdentifier());
	}

	@Test
	public void testOptOutUnreadableFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		tempFile.setReadable(false);
		tempFile.deleteOnExit();
		
		final ExecutionStatisticsCollector esc = new ExecutionStatisticsCollector(true, tempFile.getAbsolutePath());
		
		assertNull(esc.getIdentifier());
	}

	@Test
	public void testOptOutEmptyFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		tempFile.deleteOnExit();
		
		final ExecutionStatisticsCollector esc = new ExecutionStatisticsCollector(true, tempFile.getAbsolutePath());
		
		assertNull(esc.getIdentifier());
	}

	@Test
	public void testOptOutNoESCFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		Files.write(tempFile.toPath(), ("   " + ExecutionStatisticsCollector.Selection.NO_ESC.toString() + "   ").getBytes());
		tempFile.deleteOnExit();
		
		final ExecutionStatisticsCollector esc = new ExecutionStatisticsCollector(true, tempFile.getAbsolutePath());
		
		assertNull(esc.getIdentifier());
	}

	@Test
	public void testOptOutRandomIdFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		Files.write(tempFile.toPath(), ("   " + ExecutionStatisticsCollector.Selection.RANDOM_IDENTIFIER.toString() + "   ").getBytes());
		tempFile.deleteOnExit();
		
		final ExecutionStatisticsCollector esc = new ExecutionStatisticsCollector(true, tempFile.getAbsolutePath());
		
		final String identifierA = esc.getIdentifier();
		assertNotNull(identifierA);
		final String identifierB = esc.getIdentifier();
		assertNotNull(identifierB);
		assertNotEquals(identifierA, identifierB);
	}

	@Test
	public void testOptOutUserDefinedIdFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		Files.write(tempFile.toPath(), "   123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ   ".getBytes());
		tempFile.deleteOnExit();
		
		final ExecutionStatisticsCollector esc = new ExecutionStatisticsCollector(true, tempFile.getAbsolutePath());
		
		assertEquals("123456789ABCDEFGHIJKLMNOPQRSTUVW", esc.getIdentifier());
	}
	
	// Opt-In

	@Test
	public void testNoFile() {
		assertNull(new ExecutionStatisticsCollector("/path/does/not/exist").getIdentifier());
	}

	@Test
	public void testUnreadableFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		tempFile.setReadable(false);
		tempFile.deleteOnExit();
		
		assertNull(new ExecutionStatisticsCollector(tempFile.getAbsolutePath()).getIdentifier());
	}

	@Test
	public void testEmptyFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		tempFile.deleteOnExit();
		
		assertNull(new ExecutionStatisticsCollector(tempFile.getAbsolutePath()).getIdentifier());
	}

	@Test
	public void testNoESCFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		Files.write(tempFile.toPath(), ("   " + ExecutionStatisticsCollector.Selection.NO_ESC.toString() + "   ").getBytes());
		tempFile.deleteOnExit();
		
		assertNull(new ExecutionStatisticsCollector(tempFile.getAbsolutePath()).getIdentifier());
	}

	@Test
	public void testRandomIdFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		Files.write(tempFile.toPath(), ("   " + ExecutionStatisticsCollector.Selection.RANDOM_IDENTIFIER.toString() + "   ").getBytes());
		tempFile.deleteOnExit();
		
		ExecutionStatisticsCollector esc = new ExecutionStatisticsCollector(tempFile.getAbsolutePath());
		
		final String identifierA = esc.getIdentifier();
		assertNotNull(identifierA);
		final String identifierB = esc.getIdentifier();
		assertNotNull(identifierB);
		assertNotEquals(identifierA, identifierB);
	}

	@Test
	public void testUserDefinedIdFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		Files.write(tempFile.toPath(), "   123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ   ".getBytes());
		tempFile.deleteOnExit();
		
		assertEquals("123456789ABCDEFGHIJKLMNOPQRSTUVW", new ExecutionStatisticsCollector(tempFile.getAbsolutePath()).getIdentifier());
	}
}
