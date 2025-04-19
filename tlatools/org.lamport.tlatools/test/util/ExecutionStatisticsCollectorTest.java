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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assume.assumeTrue;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.HashMap;
import java.util.Map;

import org.junit.Test;

public class ExecutionStatisticsCollectorTest {

	private static class TestExecutionStatisticsCollector extends ExecutionStatisticsCollector {

		public Map<String, String> parameters;
		public String hostname;
		public boolean submitted;

		TestExecutionStatisticsCollector(String path) {
			super(path);
		}

		TestExecutionStatisticsCollector(String path, final String hostname) {
			super(path, hostname);
		}

		@Override
		protected void submit(String hostname, Map<String, String> parameters) {
			this.submitted = true;
			this.hostname = hostname;
			this.parameters = parameters;
		}
	}

	// Opt-In with company-level enabled execution statistics.

	private static final String COMPANY = "localhost";

	@Test
	public void testCompanyLevelNoFile() {
		final TestExecutionStatisticsCollector esc = new TestExecutionStatisticsCollector("/path/does/not/exist",
				COMPANY);
		assertNull(esc.getIdentifier());

		esc.collect0(new HashMap<>(Map.of("foo", "bar")));
		assertTrue(esc.submitted);
		assertEquals("bar", esc.parameters.get("foo"));
		assertEquals(COMPANY, esc.hostname);
	}

	@Test
	public void testCompanyLevelUnreadable() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		assumeTrue(tempFile.setReadable(false));       
		tempFile.deleteOnExit();

		final TestExecutionStatisticsCollector esc = new TestExecutionStatisticsCollector(tempFile.getAbsolutePath(),
				COMPANY);
		assertNull(esc.getIdentifier());

		esc.collect0(new HashMap<>(Map.of("foo", "bar")));
		assertTrue(esc.submitted);
		assertEquals("bar", esc.parameters.get("foo"));
		assertEquals(COMPANY, esc.hostname);
		final String id1 = esc.parameters.get("id");

		esc.collect0(new HashMap<>(Map.of("foo", "blub")));
		assertTrue(esc.submitted);
		assertEquals("blub", esc.parameters.get("foo"));
		assertEquals(COMPANY, esc.hostname);
		final String id2 = esc.parameters.get("id");

		// Share the same non-empty suffix, which is calculated from some of the host's
		// mac addresses.
		assertNotEquals(id1, id2);
		assertTrue(id1.length() > 20 && id2.length() > 20);
		assertEquals(id1.substring(20, id1.length()), id2.substring(20, id2.length()));
	}

	@Test
	public void testCompanyLevelEmptyFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		tempFile.deleteOnExit();

		final TestExecutionStatisticsCollector esc = new TestExecutionStatisticsCollector(tempFile.getAbsolutePath(),
				COMPANY);
		assertNull(esc.getIdentifier());

		esc.collect0(new HashMap<>(Map.of("foo", "bar")));
		assertTrue(esc.submitted);
		assertEquals("bar", esc.parameters.get("foo"));
		assertEquals(COMPANY, esc.hostname);
		final String id1 = esc.parameters.get("id");

		esc.collect0(new HashMap<>(Map.of("foo", "blub")));
		assertTrue(esc.submitted);
		assertEquals("blub", esc.parameters.get("foo"));
		assertEquals(COMPANY, esc.hostname);
		final String id2 = esc.parameters.get("id");

		// Share the same non-empty suffix, which is calculated from some of the host's
		// mac addresses.
		assertNotEquals(id1, id2);
		assertTrue(id1.length() > 20 && id2.length() > 20);
		assertEquals(id1.substring(20, id1.length()), id2.substring(20, id2.length()));
	}

	@Test
	public void testCompanyLevelNoESCFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		Files.write(tempFile.toPath(),
				("   " + ExecutionStatisticsCollector.Selection.NO_ESC.toString() + "   ").getBytes());
		tempFile.deleteOnExit();

		final TestExecutionStatisticsCollector esc = new TestExecutionStatisticsCollector(tempFile.getAbsolutePath(),
				COMPANY);
		assertNull(esc.getIdentifier());

		esc.collect0(new HashMap<>());
		assertFalse(esc.submitted);
	}

	@Test
	public void testCompanyLevelRandomIdFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		Files.write(tempFile.toPath(),
				("   " + ExecutionStatisticsCollector.Selection.RANDOM_IDENTIFIER.toString() + "   ").getBytes());
		tempFile.deleteOnExit();

		TestExecutionStatisticsCollector esc = new TestExecutionStatisticsCollector(tempFile.getAbsolutePath(),
				COMPANY);

		final String identifierA = esc.getIdentifier();
		assertNotNull(identifierA);
		final String identifierB = esc.getIdentifier();
		assertNotNull(identifierB);
		assertNotEquals(identifierA, identifierB);

		esc.collect0(new HashMap<>(Map.of("foo", "bar")));
		assertTrue(esc.submitted);
		assertEquals(COMPANY, esc.hostname);
		assertEquals("bar", esc.parameters.get("foo"));
		assertNotEquals(identifierA, esc.parameters.get("id"));
		assertNotEquals(identifierB, esc.parameters.get("id"));
		final String id1 = esc.parameters.get("id");

		esc.collect0(new HashMap<>(Map.of("foo", "bar")));
		assertTrue(esc.submitted);
		assertEquals(COMPANY, esc.hostname);
		assertEquals("bar", esc.parameters.get("foo"));
		assertNotEquals(identifierA, esc.parameters.get("id"));
		assertNotEquals(identifierB, esc.parameters.get("id"));
		final String id2 = esc.parameters.get("id");

		assertNotEquals(id1, id2);
		assertTrue(id1.length() > 20 && id2.length() > 20);
		assertNotEquals(id1.substring(20, id1.length()), id2.substring(20, id2.length()));
	}

	@Test
	public void testCompanyLevelUserDefinedIdFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		Files.write(tempFile.toPath(), "   123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ   ".getBytes());
		tempFile.deleteOnExit();

		final TestExecutionStatisticsCollector esc = new TestExecutionStatisticsCollector(tempFile.getAbsolutePath(),
				COMPANY);
		assertEquals("123456789ABCDEFGHIJKLMNOPQRSTUVW", esc.getIdentifier());

		esc.collect0(new HashMap<>(Map.of("foo", "bar")));
		assertTrue(esc.submitted);
		assertEquals("bar", esc.parameters.get("foo"));
		assertEquals(COMPANY, esc.hostname);
		assertEquals("123456789ABCDEFGHIJKLMNOPQRSTUVW", esc.parameters.get("id"));
	}

	// Opt-In

	@Test
	public void testNoFile() {
		final TestExecutionStatisticsCollector esc = new TestExecutionStatisticsCollector("/path/does/not/exist");
		assertNull(esc.getIdentifier());

		esc.collect0(new HashMap<>());
		assertFalse(esc.submitted);
	}

	@Test
	public void testUnreadableFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		assumeTrue(tempFile.setReadable(false));
		tempFile.deleteOnExit();

		final TestExecutionStatisticsCollector esc = new TestExecutionStatisticsCollector(tempFile.getAbsolutePath());
		assertNull(esc.getIdentifier());

		esc.collect0(new HashMap<>());
		assertFalse(esc.submitted);
	}

	@Test
	public void testEmptyFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		tempFile.deleteOnExit();

		final TestExecutionStatisticsCollector esc = new TestExecutionStatisticsCollector(tempFile.getAbsolutePath());
		assertNull(esc.getIdentifier());

		esc.collect0(new HashMap<>());
		assertFalse(esc.submitted);
	}

	@Test
	public void testNoESCFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		Files.write(tempFile.toPath(),
				("   " + ExecutionStatisticsCollector.Selection.NO_ESC.toString() + "   ").getBytes());
		tempFile.deleteOnExit();

		final TestExecutionStatisticsCollector esc = new TestExecutionStatisticsCollector(tempFile.getAbsolutePath());
		assertNull(esc.getIdentifier());

		esc.collect0(new HashMap<>());
		assertFalse(esc.submitted);
	}

	@Test
	public void testRandomIdFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		Files.write(tempFile.toPath(),
				("   " + ExecutionStatisticsCollector.Selection.RANDOM_IDENTIFIER.toString() + "   ").getBytes());
		tempFile.deleteOnExit();

		TestExecutionStatisticsCollector esc = new TestExecutionStatisticsCollector(tempFile.getAbsolutePath());

		final String identifierA = esc.getIdentifier();
		assertNotNull(identifierA);
		final String identifierB = esc.getIdentifier();
		assertNotNull(identifierB);
		assertNotEquals(identifierA, identifierB);

		esc.collect0(new HashMap<>(Map.of("foo", "bar")));
		assertTrue(esc.submitted);
		assertEquals("esc01.tlapl.us", esc.hostname);
		assertEquals("bar", esc.parameters.get("foo"));
		assertNotEquals(identifierA, esc.parameters.get("id"));
		assertNotEquals(identifierB, esc.parameters.get("id"));
	}

	@Test
	public void testUserDefinedIdFile() throws IOException {
		File tempFile = File.createTempFile("esc", "txt");
		Files.write(tempFile.toPath(), "   123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ   ".getBytes());
		tempFile.deleteOnExit();

		final TestExecutionStatisticsCollector esc = new TestExecutionStatisticsCollector(tempFile.getAbsolutePath());
		assertEquals("123456789ABCDEFGHIJKLMNOPQRSTUVW", esc.getIdentifier());

		esc.collect0(new HashMap<>(Map.of("foo", "bar")));
		assertTrue(esc.submitted);
		assertEquals("bar", esc.parameters.get("foo"));
		assertEquals("esc01.tlapl.us", esc.hostname);
		assertEquals("123456789ABCDEFGHIJKLMNOPQRSTUVW", esc.parameters.get("id"));
	}
}
