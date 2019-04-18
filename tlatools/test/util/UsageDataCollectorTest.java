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

public class UsageDataCollectorTest {

	// Opt-out

	@Test
	public void testMCNoFile() throws IOException {
		final String tmpdir = System.getProperty("java.io.tmpdir");
		final File tempFile = new File(tmpdir + File.separator + "udc" + System.currentTimeMillis() + ".txt");
		tempFile.deleteOnExit();
		
		final UsageDataCollector udc = new UsageDataCollector(true, tempFile.getAbsolutePath());
		
		final String identifierA = udc.getIdentifier();
		assertNotNull(identifierA);
		assertNotNull(udc.getIdentifier());
		assertEquals(identifierA, udc.getIdentifier());
	}

	@Test
	public void testMCUnreadableFile() throws IOException {
		File tempFile = File.createTempFile("udc", "txt");
		tempFile.setReadable(false);
		tempFile.deleteOnExit();
		
		final UsageDataCollector udc = new UsageDataCollector(true, tempFile.getAbsolutePath());
		
		assertNull(udc.getIdentifier());
	}

	@Test
	public void testMCEmptyFile() throws IOException {
		File tempFile = File.createTempFile("udc", "txt");
		tempFile.deleteOnExit();
		
		final UsageDataCollector udc = new UsageDataCollector(true, tempFile.getAbsolutePath());
		
		assertNull(udc.getIdentifier());
	}

	@Test
	public void testMCNoUDCFile() throws IOException {
		File tempFile = File.createTempFile("udc", "txt");
		Files.write(tempFile.toPath(), "   NO_UDC   ".getBytes());
		tempFile.deleteOnExit();
		
		final UsageDataCollector udc = new UsageDataCollector(true, tempFile.getAbsolutePath());
		
		assertNull(udc.getIdentifier());
	}

	@Test
	public void testMCRandomIdFile() throws IOException {
		File tempFile = File.createTempFile("udc", "txt");
		Files.write(tempFile.toPath(), "   RANDOM_IDENTIFIER   ".getBytes());
		tempFile.deleteOnExit();
		
		final UsageDataCollector udc = new UsageDataCollector(true, tempFile.getAbsolutePath());
		
		final String identifierA = udc.getIdentifier();
		assertNotNull(identifierA);
		final String identifierB = udc.getIdentifier();
		assertNotNull(identifierB);
		assertNotEquals(identifierA, identifierB);
	}

	@Test
	public void testMCUserDefinedIdFile() throws IOException {
		File tempFile = File.createTempFile("udc", "txt");
		Files.write(tempFile.toPath(), "   123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ   ".getBytes());
		tempFile.deleteOnExit();
		
		final UsageDataCollector udc = new UsageDataCollector(true, tempFile.getAbsolutePath());
		
		assertEquals("123456789ABCDEFGHIJKLMNOPQRSTUVW", udc.getIdentifier());
	}
	
	// Opt-In

	@Test
	public void testNoFile() {
		assertNull(new UsageDataCollector("/path/does/not/exist").getIdentifier());
	}

	@Test
	public void testUnreadableFile() throws IOException {
		File tempFile = File.createTempFile("udc", "txt");
		tempFile.setReadable(false);
		tempFile.deleteOnExit();
		
		assertNull(new UsageDataCollector(tempFile.getAbsolutePath()).getIdentifier());
	}

	@Test
	public void testEmptyFile() throws IOException {
		File tempFile = File.createTempFile("udc", "txt");
		tempFile.deleteOnExit();
		
		assertNull(new UsageDataCollector(tempFile.getAbsolutePath()).getIdentifier());
	}

	@Test
	public void testNoUDCFile() throws IOException {
		File tempFile = File.createTempFile("udc", "txt");
		Files.write(tempFile.toPath(), "   NO_UDC   ".getBytes());
		tempFile.deleteOnExit();
		
		assertNull(new UsageDataCollector(tempFile.getAbsolutePath()).getIdentifier());
	}

	@Test
	public void testRandomIdFile() throws IOException {
		File tempFile = File.createTempFile("udc", "txt");
		Files.write(tempFile.toPath(), "   RANDOM_IDENTIFIER   ".getBytes());
		tempFile.deleteOnExit();
		
		UsageDataCollector udc = new UsageDataCollector(tempFile.getAbsolutePath());
		
		final String identifierA = udc.getIdentifier();
		assertNotNull(identifierA);
		final String identifierB = udc.getIdentifier();
		assertNotNull(identifierB);
		assertNotEquals(identifierA, identifierB);
	}

	@Test
	public void testUserDefinedIdFile() throws IOException {
		File tempFile = File.createTempFile("udc", "txt");
		Files.write(tempFile.toPath(), "   123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ   ".getBytes());
		tempFile.deleteOnExit();
		
		assertEquals("123456789ABCDEFGHIJKLMNOPQRSTUVW", new UsageDataCollector(tempFile.getAbsolutePath()).getIdentifier());
	}
}
