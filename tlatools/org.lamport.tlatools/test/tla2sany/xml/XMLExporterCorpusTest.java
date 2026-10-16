/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
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
 ******************************************************************************/
package tla2sany.xml;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.io.StringReader;
import java.net.URL;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.nio.file.Paths;
import java.util.List;
import java.util.stream.Collectors;

import javax.xml.XMLConstants;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;
import javax.xml.validation.Validator;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.w3c.dom.Document;
import org.xml.sax.InputSource;

import util.ToolIO;

/**
 * Comprehensive corpus test for XMLExporter that validates it can successfully
 * export all TLA+ modules in the test-model directory.
 *
 * This test discovers all .tla files in test-model/ and runs XMLExporter on
 * each, validating that: 1. XMLExporter exits with code 0 (success) 2. XML
 * output is well-formed 3. XML output validates against the sany.xsd schema
 *
 * If any file fails, the test reports which specific file had the issue.
 */
@RunWith(Parameterized.class)
public class XMLExporterCorpusTest {

	private static final String BASE_DIR = System.getProperty("basedir", System.getProperty("user.dir", "."));
	private static final String TEST_MODEL_DIR = BASE_DIR + File.separator + "test-model";

	/**
	 * Test case wrapper for a single .tla file
	 */
	private static class TestCase {
		private final Path filePath;
		private final String relativePath;

		public TestCase(Path filePath) {
			this.filePath = filePath;
			// Create a readable relative path for test output
			Path base = Paths.get(TEST_MODEL_DIR);
			this.relativePath = base.relativize(filePath).toString();
		}

		public String getAbsolutePath() {
			return filePath.toAbsolutePath().toString();
		}

		@Override
		public String toString() {
			return relativePath;
		}
	}

	/**
	 * Discovers all .tla files in test-model/ directory recursively.
	 */
	@Parameters(name = "{index}: {0}")
	public static List<TestCase> getTestFiles() throws IOException {
		Path testModelDir = Paths.get(TEST_MODEL_DIR);
		PathMatcher matcher = FileSystems.getDefault().getPathMatcher("glob:**/*.tla");

		return Files.walk(testModelDir).filter(Files::isRegularFile).filter(matcher::matches).sorted() // Sort for
																										// consistent
																										// test ordering
				.map(TestCase::new).collect(Collectors.toList());
	}

	/**
	 * The current test file
	 */
	@Parameter
	public TestCase testCase;

	private final ByteArrayOutputStream outStream = new ByteArrayOutputStream();
	private final ByteArrayOutputStream errStream = new ByteArrayOutputStream();

	@Before
	public void captureOutput() {
		ToolIO.out = new PrintStream(this.outStream);
		ToolIO.err = new PrintStream(this.errStream);
	}

	/**
	 * Test that XMLExporter can successfully parse and export the module to valid
	 * XML.
	 */
	@Test
	public void testExportModule() throws Exception {
		String modulePath = testCase.getAbsolutePath();

		// Run XMLExporter
		int exitCode = XMLExporter.run(modulePath);

		// Get outputs for diagnostics
		String xmlOutput = this.outStream.toString();
		String errOutput = this.errStream.toString();

		// ASSERTION 1: XMLExporter should exit with code 0
		// If this fails, check stderr for parse errors or other issues
		Assert.assertEquals("XMLExporter failed for " + testCase + ". Stderr: " + errOutput, 0, exitCode);

		// ASSERTION 2: XML output should not be empty
		Assert.assertFalse("XML output is empty for " + testCase, xmlOutput.trim().isEmpty());

		// ASSERTION 3: XML should be well-formed (parseable)
		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		factory.setNamespaceAware(true);
		DocumentBuilder builder = factory.newDocumentBuilder();
		Document doc;
		try {
			doc = builder.parse(new InputSource(new StringReader(xmlOutput)));
		} catch (Exception e) {
			Assert.fail("XML is not well-formed for " + testCase + ": " + e.getMessage());
			return; // Unreachable but needed for compilation
		}

		// ASSERTION 4: XML should validate against XSD schema
		SchemaFactory schemaFactory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
		URL schemaFile = XMLExporter.class.getResource("sany.xsd");
		Assert.assertNotNull("sany.xsd schema file should be found", schemaFile);

		Schema schema = schemaFactory.newSchema(schemaFile);
		Validator validator = schema.newValidator();

		try {
			validator.validate(new DOMSource(doc));
		} catch (Exception e) {
			Assert.fail("XML does not validate against schema for " + testCase + ": " + e.getMessage());
		}
	}
}
