/*******************************************************************************
 * Copyright (c) 2025 TLA+ Foundation. All rights reserved. 
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
import java.io.PrintStream;
import java.io.StringReader;
import java.net.URL;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

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
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;

import util.ToolIO;

/**
 * Test XMLExporter with a non-trivial TLA+ module from test-model directory.
 * This test validates that the XMLExporter correctly parses and exports the
 * DieHard.tla module to XML format. This test was written by AI.
 */
public class TestXMLExporterModule {

	private static final String BASE_DIR = System.getProperty("basedir", System.getProperty("user.dir", "."));
	private static final String TEST_MODEL = "test-model" + File.separator;
	private static final String BASE_PATH = System.getProperty("basepath", BASE_DIR + File.separator + TEST_MODEL);

	private final ByteArrayOutputStream outStream = new ByteArrayOutputStream();
	private final ByteArrayOutputStream errStream = new ByteArrayOutputStream();

	@Before
	public void captureOutput() {
		ToolIO.out = new PrintStream(this.outStream);
		ToolIO.err = new PrintStream(this.errStream);
	}

	@Test
	public void testExportDieHardModule() throws Exception {
		// Run XMLExporter on DieHard.tla
		String modulePath = BASE_PATH + "DieHard.tla";
		int exitCode = XMLExporter.run(modulePath);

		// Verify successful execution
		Assert.assertEquals("XMLExporter should exit with code 0", 0, exitCode);

		// Get the XML output
		String xmlOutput = this.outStream.toString();
		String errOutput = this.errStream.toString();

		// Verify no stderr output (trim whitespace)
		Assert.assertTrue("No errors should be written to stderr", errOutput.trim().isEmpty());

		// Verify XML output is not empty
		Assert.assertFalse("XML output should not be empty", xmlOutput.trim().isEmpty());

		// Parse the XML to verify it's well-formed
		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		factory.setNamespaceAware(true);
		DocumentBuilder builder = factory.newDocumentBuilder();
		Document doc = builder.parse(new InputSource(new StringReader(xmlOutput)));

		// Validate against XSD schema (same as XMLExporter does)
		SchemaFactory schemaFactory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
		URL schemaFile = XMLExporter.class.getResource("sany.xsd");
		Assert.assertNotNull("sany.xsd schema file should be found", schemaFile);
		Schema schema = schemaFactory.newSchema(schemaFile);
		Validator validator = schema.newValidator();
		validator.validate(new DOMSource(doc));

		// --- Root Element Checks ---
		Element root = doc.getDocumentElement();
		Assert.assertNotNull("Root element should exist", root);
		Assert.assertEquals("Root element should be 'modules'", "modules", root.getNodeName());

		// --- RootModule Check ---
		NodeList rootModuleNodes = root.getElementsByTagName("RootModule");
		Assert.assertEquals("Should have exactly one RootModule element", 1, rootModuleNodes.getLength());
		Element rootModule = (Element) rootModuleNodes.item(0);
		String rootModuleName = rootModule.getTextContent().trim();
		Assert.assertEquals("Root module should be DieHard", "DieHard", rootModuleName);

		// RootModule should have a 'filename' attribute (if exporter includes it)
		if (rootModule.hasAttribute("filename")) {
			String filenameAttr = rootModule.getAttribute("filename");
			Assert.assertTrue("filename attribute should end with DieHard.tla", filenameAttr.endsWith("DieHard.tla"));
		}

		// --- Context Check ---
		NodeList contextNodes = root.getElementsByTagName("context");
		Assert.assertEquals("Should have exactly one context element", 1, contextNodes.getLength());

		// --- ModuleNode Check ---
		NodeList moduleNodes = root.getElementsByTagName("ModuleNode");
		Assert.assertTrue("Should have at least one ModuleNode", moduleNodes.getLength() > 0);

		// Locate DieHard ModuleNode
		Element dieHardModule = null;
		for (int i = 0; i < moduleNodes.getLength(); i++) {
			Element module = (Element) moduleNodes.item(i);
			NodeList uniqueNames = module.getElementsByTagName("uniquename");
			if (uniqueNames.getLength() > 0) {
				String name = uniqueNames.item(0).getTextContent().trim();
				if ("DieHard".equals(name)) {
					dieHardModule = module;
					break;
				}
			}
		}
		Assert.assertNotNull("DieHard module should be found in XML", dieHardModule);

		// --- Operator Checks ---

		// Verify the DieHard module contains expected operators
		// The module should contain Min, Init, Next, Spec, Inv, and FixWater
		String[] expectedOperators = { "Min", "Init", "Next", "Spec", "Inv", "FixWater" };
		for (String opName : expectedOperators) {
			boolean found = xmlOutput.contains(">" + opName + "<");
			Assert.assertTrue("XML should contain operator: " + opName, found);
		}

		// --- Constants Checks ---
		String[] expectedConstants = { "NONDET", "FILL_BIG", "EMPTY_BIG", "FILL_SMALL", "EMPTY_SMALL", "BIG_TO_SMALL",
				"SMALL_TO_BIG" };
		for (String constName : expectedConstants) {
			boolean found = xmlOutput.contains(">" + constName + "<");
			Assert.assertTrue("XML should contain constant: " + constName, found);
		}

		// --- Variable Checks ---
		String[] expectedVariables = { "bigBucket", "smallBucket", "action", "water_to_pour" };
		for (String varName : expectedVariables) {
			boolean found = xmlOutput.contains(">" + varName + "<");
			Assert.assertTrue("XML should contain variable: " + varName, found);
		}

		// --- Optional Sanity: Ensure no unexpected top-level modules ---
		Set<String> expectedModuleNames = Set.of("DieHard", "Naturals", "Integers", "Sequences", "FiniteSets", "TLC");
		for (int i = 0; i < moduleNodes.getLength(); i++) {
			Element module = (Element) moduleNodes.item(i);
			String name = module.getElementsByTagName("uniquename").item(0).getTextContent().trim();
			Assert.assertTrue("Unexpected module: " + name, expectedModuleNames.contains(name));
		}
	}

	@Test
	public void testExportCaseOtherModule() throws Exception {
		String modulePath = BASE_PATH + "CaseOtherXml.tla";
		int exitCode = XMLExporter.run(modulePath);

		Assert.assertEquals("XMLExporter should exit with code 0", 0, exitCode);

		String xmlOutput = this.outStream.toString();
		Assert.assertFalse("XML output should not be empty", xmlOutput.trim().isEmpty());

		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		factory.setNamespaceAware(true);
		DocumentBuilder builder = factory.newDocumentBuilder();
		Document doc = builder.parse(new InputSource(new StringReader(xmlOutput)));

		SchemaFactory schemaFactory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
		URL schemaFile = XMLExporter.class.getResource("sany.xsd");
		Assert.assertNotNull("sany.xsd schema file should be found", schemaFile);
		Schema schema = schemaFactory.newSchema(schemaFile);
		Validator validator = schema.newValidator();
		validator.validate(new DOMSource(doc));

		NodeList stringNodes = doc.getElementsByTagName("StringNode");
		boolean foundOther = false;
		for (int i = 0; i < stringNodes.getLength(); i++) {
			Element stringNode = (Element) stringNodes.item(i);
			NodeList valueNodes = stringNode.getElementsByTagName("StringValue");
			if (valueNodes.getLength() > 0) {
				String value = valueNodes.item(0).getTextContent().trim();
				if ("$Other".equals(value)) {
					foundOther = true;
					break;
				}
			}
		}
		Assert.assertTrue("XML should contain StringNode/StringValue '$Other'", foundOther);
	}

	@Test
	public void testExportWithOfflineMode() throws Exception {
		// Run XMLExporter with offline mode (skip validation)
		String modulePath = BASE_PATH + "DieHard.tla";
		int exitCode = XMLExporter.run("-o", modulePath);

		// Verify successful execution
		Assert.assertEquals("XMLExporter should exit with code 0", 0, exitCode);

		// Get the XML output
		String xmlOutput = this.outStream.toString();

		// Verify XML output is not empty
		Assert.assertNotEquals("XML output should not be empty", 0, xmlOutput.length());

		// Verify it's still valid XML and well-formed
		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		factory.setNamespaceAware(true);
		DocumentBuilder builder = factory.newDocumentBuilder();
		Document doc = builder.parse(new InputSource(new StringReader(xmlOutput)));

		Assert.assertNotNull("Document should be parsed successfully", doc);

		// Note: In offline mode, XMLExporter skips validation, but we can still
		// validate
		// to ensure the output conforms to the schema
		SchemaFactory schemaFactory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
		URL schemaFile = XMLExporter.class.getResource("sany.xsd");
		if (schemaFile != null) {
			Schema schema = schemaFactory.newSchema(schemaFile);
			Validator validator = schema.newValidator();
			validator.validate(new DOMSource(doc));
		}
	}

	@Test
	public void testExportWithTerseMode() throws Exception {
		// Run XMLExporter with terse mode (no pretty printing)
		String modulePath = BASE_PATH + "DieHard.tla";
		int exitCode = XMLExporter.run("-t", modulePath);

		// Verify successful execution
		Assert.assertEquals("XMLExporter should exit with code 0", 0, exitCode);

		// Get the XML output
		String xmlOutput = this.outStream.toString();

		// Verify XML output is not empty
		Assert.assertNotEquals("XML output should not be empty", 0, xmlOutput.length());

		// Verify it's still valid XML and validates against schema
		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		factory.setNamespaceAware(true);
		DocumentBuilder builder = factory.newDocumentBuilder();
		Document doc = builder.parse(new InputSource(new StringReader(xmlOutput)));

		Assert.assertNotNull("Document should be parsed successfully in terse mode", doc);

		// Validate against XSD schema
		SchemaFactory schemaFactory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
		URL schemaFile = XMLExporter.class.getResource("sany.xsd");
		Assert.assertNotNull("sany.xsd schema file should be found", schemaFile);
		Schema schema = schemaFactory.newSchema(schemaFile);
		Validator validator = schema.newValidator();
		validator.validate(new DOMSource(doc));
	}

	@Test
	public void testExportWithRestrictedMode() throws Exception {
		// Run XMLExporter with restricted mode (only the root module)
		String modulePath = BASE_PATH + "DieHard.tla";
		int exitCode = XMLExporter.run("-r", modulePath);

		// Verify successful execution
		Assert.assertEquals("XMLExporter should exit with code 0", 0, exitCode);

		// Get the XML output
		String xmlOutput = this.outStream.toString();

		// Verify XML output is not empty
		Assert.assertNotEquals("XML output should not be empty", 0, xmlOutput.length());

		// Verify it's still valid XML and validates against schema
		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		factory.setNamespaceAware(true);
		DocumentBuilder builder = factory.newDocumentBuilder();
		Document doc = builder.parse(new InputSource(new StringReader(xmlOutput)));

		Assert.assertNotNull("Document should be parsed successfully in restricted mode", doc);

		// Validate against XSD schema
		SchemaFactory schemaFactory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
		URL schemaFile = XMLExporter.class.getResource("sany.xsd");
		Assert.assertNotNull("sany.xsd schema file should be found", schemaFile);
		Schema schema = schemaFactory.newSchema(schemaFile);
		Validator validator = schema.newValidator();
		validator.validate(new DOMSource(doc));

		// In restricted mode, extended modules' definitions should be excluded
		// But the DieHard module itself should still be present
		Element root = doc.getDocumentElement();
		NodeList rootModuleNodes = root.getElementsByTagName("RootModule");
		Assert.assertEquals("Should have exactly one RootModule element", 1, rootModuleNodes.getLength());
	}

	@Test
	public void testRelationPreComments() throws Exception {
		// Run XMLExporter on Relation.tla module which contains comments for each
		// operator
		String modulePath = BASE_PATH + "Echo" + File.separator + "Relation.tla";
		int exitCode = XMLExporter.run(modulePath);

		// Verify successful execution
		Assert.assertEquals("XMLExporter should exit with code 0", 0, exitCode);

		// Get the XML output
		String xmlOutput = this.outStream.toString();
		String errOutput = this.errStream.toString();

		// Verify no stderr output
		Assert.assertTrue("No errors should be written to stderr", errOutput.trim().isEmpty());

		// Verify XML output is not empty
		Assert.assertFalse("XML output should not be empty", xmlOutput.trim().isEmpty());

		// Parse the XML to verify it's well-formed
		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		factory.setNamespaceAware(true);
		DocumentBuilder builder = factory.newDocumentBuilder();
		Document doc = builder.parse(new InputSource(new StringReader(xmlOutput)));

		// Validate against XSD schema
		SchemaFactory schemaFactory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
		URL schemaFile = XMLExporter.class.getResource("sany.xsd");
		Assert.assertNotNull("sany.xsd schema file should be found", schemaFile);
		Schema schema = schemaFactory.newSchema(schemaFile);
		Validator validator = schema.newValidator();
		validator.validate(new DOMSource(doc));

		// --- Verify pre-comments are present ---
		Element root = doc.getDocumentElement();
		NodeList preCommentsNodes = root.getElementsByTagName("pre-comments");

		// There should be at least some pre-comments in the Relation module
		Assert.assertTrue("Relation module should have operators with pre-comments", preCommentsNodes.getLength() > 0);

		// Define expected comment content for each operator
		Map<String, String> expectedComments = new HashMap<>(Map.of(
			"IsReflexive", "Is the relation R reflexive over S?",
			"IsIrreflexive", "Is the relation R irreflexive over set S?",
			"IsSymmetric", "Is the relation R symmetric over set S?",
			"IsAsymmetric", "Is the relation R asymmetric over set S?",
			"IsTransitive", "Is the relation R transitive over set S?",
			"TransitiveClosure", "Compute the transitive closure of relation R over set S",
			"ReflexiveTransitiveClosure", "Compute the reflexive transitive closure of relation R over set S",
			"IsConnected", "Is the relation R connected over set S"
		));

		for (int i = 0; i < preCommentsNodes.getLength(); i++) {
			Element preComment = (Element) preCommentsNodes.item(i);
			String commentText = preComment.getTextContent();

			// Pre-comments should not be empty
			Assert.assertFalse("Pre-comment should not be empty", commentText.trim().isEmpty());

			Element parent = (Element) preComment.getParentNode();
			NodeList uniqueNames = parent.getElementsByTagName("uniquename");
			if (uniqueNames.getLength() == 0)
				continue;

			String opName = uniqueNames.item(0).getTextContent().trim();

			String expected = expectedComments.get(opName);
			if (expected != null && commentText.contains(expected)) {
				// Found this operator's comment, remove it from the map
				expectedComments.remove(opName);
			}
		}

		// Assert that all expected comments were found
		Assert.assertTrue("Missing expected operator comments: " + expectedComments.keySet(), expectedComments.isEmpty());
	}

	@Test
	public void testTLACommentStylesPreComments() throws Exception {
		// Run XMLExporter on TLACommentStyles.tla module which demonstrates all TLA+
		// comment styles
		String modulePath = BASE_PATH + "TLACommentStyles.tla";
		int exitCode = XMLExporter.run(modulePath);

		// Verify successful execution
		Assert.assertEquals("XMLExporter should exit with code 0", 0, exitCode);

		// Get the XML output
		String xmlOutput = this.outStream.toString();
		String errOutput = this.errStream.toString();

		// Verify no stderr output
		Assert.assertTrue("No errors should be written to stderr", errOutput.trim().isEmpty());

		// Verify XML output is not empty
		Assert.assertFalse("XML output should not be empty", xmlOutput.trim().isEmpty());

		// Parse the XML to verify it's well-formed
		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		factory.setNamespaceAware(true);
		DocumentBuilder builder = factory.newDocumentBuilder();
		Document doc = builder.parse(new InputSource(new StringReader(xmlOutput)));

		// Validate against XSD schema
		SchemaFactory schemaFactory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
		URL schemaFile = XMLExporter.class.getResource("sany.xsd");
		Assert.assertNotNull("sany.xsd schema file should be found", schemaFile);
		Schema schema = schemaFactory.newSchema(schemaFile);
		Validator validator = schema.newValidator();
		validator.validate(new DOMSource(doc));

		// --- Verify pre-comments are present ---
		Element root = doc.getDocumentElement();
		NodeList preCommentsNodes = root.getElementsByTagName("pre-comments");

		// There should be pre-comments in the TLACommentStyles module
		Assert.assertEquals("TLACommentStyles module should have operators with pre-comments", 4,
				preCommentsNodes.getLength());

		// Define expected comment content for each style
		Map<String, String> expectedComments = new HashMap<>(Map.of(
			    "CommentStyle1", 
			        "(*************************************************************************)\n" +
			        "(* Calculate the sum of projections of the elements in a set.            *)\n" +
			        "(*                                                                       *)\n" +
			        "(* Example:                                                              *)\n" +
			        "(*         MapThenSumSet(                                                *)\n" +
			        "(*             LAMBDA e : e.n,                                           *)\n" +
			        "(*             {[n |-> 0], [n |-> 1], [n |-> 2]}                         *)\n" +
			        "(*         ) = 3                                                         *)\n" +
			        "(*************************************************************************)",
			    "CommentStyle2", 
			        "(*************************************************************************)\n" +
			        "(* COMMENT STYLE 2: Indented Boxed Comment                              *)\n" +
			        "(* Used for nested or secondary explanations.                           *)\n" +
			        "(* Note the indentation at the start.                                   *)\n" +
			        "(*************************************************************************)",
			    "CommentStyle3", 
			        "(* COMMENT STYLE 3: Simple Multi-line Comment Without Box\n" +
			        "   This style doesn't use asterisks on every line.\n" +
			        "   It's more free-form and less structured.\n" +
			        "   Often used for algorithm descriptions or citations.\n" +
			        " *)",
			    "CommentStyle4", 
			        "\\* Declaring instances local causes definition overrides to be hidden. In the\n" +
			        "\\* case of Toolbox, this causes the definition override of `_TETrace` to be\n" +
			        "\\* invisible.  In turn, TLC will then try to evaluate the TLA+ definition of\n" +
			        "\\*\n" +
			        "\\* `_TETrace` as defined in Tooblox.tla:\n" +
			        "\\*   Attempted to enumerate S \\ T when S:\n" +
			        "\\*   Nat\n" +
			        "\\*   is not enumerable.\n" +
			        "\\*\n" +
			        "\\* See: https://github.com/tlaplus/CommunityModules/issues/37"
		));

		for (int i = 0; i < preCommentsNodes.getLength(); i++) {
			Element preComment = (Element) preCommentsNodes.item(i);
			String commentText = preComment.getTextContent();

			Element parent = (Element) preComment.getParentNode();
			NodeList uniqueNames = parent.getElementsByTagName("uniquename");
			if (uniqueNames.getLength() == 0)
				continue;

			String opName = uniqueNames.item(0).getTextContent().trim();

			String expected = expectedComments.get(opName);
			if (expected != null && commentText.equals(expected)) {
				// Found this style, remove it from the map
				expectedComments.remove(opName);
			}
		}

		// Assert that all expected comment styles were found
		Assert.assertTrue("Missing expected comment styles: " + expectedComments.keySet(), expectedComments.isEmpty());
	}

	@Test
	public void testUncommentFlagWithTLACommentStyles() throws Exception {
		// Run XMLExporter with -u flag on TLACommentStyles.tla module
		String modulePath = BASE_PATH + "TLACommentStyles.tla";
		int exitCode = XMLExporter.run("-u", modulePath);

		// Verify successful execution
		Assert.assertEquals("XMLExporter should exit with code 0", 0, exitCode);

		// Get the XML output
		String xmlOutput = this.outStream.toString();
		String errOutput = this.errStream.toString();

		// Verify no stderr output
		Assert.assertTrue("No errors should be written to stderr", errOutput.trim().isEmpty());

		// Verify XML output is not empty
		Assert.assertFalse("XML output should not be empty", xmlOutput.trim().isEmpty());

		// Parse the XML to verify it's well-formed
		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		factory.setNamespaceAware(true);
		DocumentBuilder builder = factory.newDocumentBuilder();
		Document doc = builder.parse(new InputSource(new StringReader(xmlOutput)));

		// Validate against XSD schema
		SchemaFactory schemaFactory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
		URL schemaFile = XMLExporter.class.getResource("sany.xsd");
		Assert.assertNotNull("sany.xsd schema file should be found", schemaFile);
		Schema schema = schemaFactory.newSchema(schemaFile);
		Validator validator = schema.newValidator();
		validator.validate(new DOMSource(doc));

		// --- Verify pre-comments are processed with uncomment ---
		Element root = doc.getDocumentElement();
		NodeList preCommentsNodes = root.getElementsByTagName("pre-comments");

		// There should be pre-comments in the TLACommentStyles module
		Assert.assertEquals("TLACommentStyles module should have operators with pre-comments", 4,
				preCommentsNodes.getLength());

		// With -u flag, boxed comments should have their box formatting removed
		Map<String, String> expectedUncommentedContent = new HashMap<>(Map.of(
			    "CommentStyle1", 
			        "Calculate the sum of projections of the elements in a set.\n" +
			        "\n" +
			        "Example:\n" +
			        "        MapThenSumSet(\n" +
			        "            LAMBDA e : e.n,\n" +
			        "            {[n |-> 0], [n |-> 1], [n |-> 2]}\n" +
			        "        ) = 3",
			    "CommentStyle2", 
			        "COMMENT STYLE 2: Indented Boxed Comment\n" +
			        "Used for nested or secondary explanations.\n" +
			        "Note the indentation at the start.",
			    "CommentStyle4",
			        "Declaring instances local causes definition overrides to be hidden. In the\n" +
			        "case of Toolbox, this causes the definition override of `_TETrace` to be\n" +
			        "invisible.  In turn, TLC will then try to evaluate the TLA+ definition of\n" +
			        "\n" +
			        "`_TETrace` as defined in Tooblox.tla:\n" +
			        "  Attempted to enumerate S \\ T when S:\n" +
			        "  Nat\n" +
			        "  is not enumerable.\n" +
			        "\n" +
			        "See: https://github.com/tlaplus/CommunityModules/issues/37"
		));

		for (int i = 0; i < preCommentsNodes.getLength(); i++) {
			Element preComment = (Element) preCommentsNodes.item(i);
			String commentText = preComment.getTextContent();

			Element parent = (Element) preComment.getParentNode();
			NodeList uniqueNames = parent.getElementsByTagName("uniquename");
			if (uniqueNames.getLength() == 0)
				continue;

			String opName = uniqueNames.item(0).getTextContent().trim();

			String expected = expectedUncommentedContent.get(opName);
			if (expected != null) {
				Assert.assertTrue("Comment for " + opName + " should be uncommented and contain expected content",
						commentText.contains(expected));
				expectedUncommentedContent.remove(opName);
			}
		}

		// Assert that all expected uncommented content was found
		Assert.assertTrue("Missing expected uncommented content for: " + expectedUncommentedContent.keySet(),
				expectedUncommentedContent.isEmpty());
	}

	@Test
	public void testUncommentFlagWithRelations() throws Exception {
		// Run XMLExporter with -u flag on Relation.tla module
		String modulePath = BASE_PATH + "Echo" + File.separator + "Relation.tla";
		int exitCode = XMLExporter.run("-u", modulePath);

		// Verify successful execution
		Assert.assertEquals("XMLExporter should exit with code 0", 0, exitCode);

		// Get the XML output
		String xmlOutput = this.outStream.toString();
		String errOutput = this.errStream.toString();

		// Verify no stderr output
		Assert.assertTrue("No errors should be written to stderr", errOutput.trim().isEmpty());

		// Verify XML output is not empty
		Assert.assertFalse("XML output should not be empty", xmlOutput.trim().isEmpty());

		// Parse the XML to verify it's well-formed
		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		factory.setNamespaceAware(true);
		DocumentBuilder builder = factory.newDocumentBuilder();
		Document doc = builder.parse(new InputSource(new StringReader(xmlOutput)));

		// Validate against XSD schema
		SchemaFactory schemaFactory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
		URL schemaFile = XMLExporter.class.getResource("sany.xsd");
		Assert.assertNotNull("sany.xsd schema file should be found", schemaFile);
		Schema schema = schemaFactory.newSchema(schemaFile);
		Validator validator = schema.newValidator();
		validator.validate(new DOMSource(doc));

		// --- Verify pre-comments are processed with uncomment ---
		Element root = doc.getDocumentElement();
		NodeList preCommentsNodes = root.getElementsByTagName("pre-comments");

		// There should be at least some pre-comments in the Relation module
		Assert.assertTrue("Relation module should have operators with pre-comments", preCommentsNodes.getLength() > 0);

		// With -u flag, the boxed comments should have their formatting removed
		// The actual comment content should still be present but without the box characters
		Map<String, String> expectedUncommentedContent = new HashMap<>(Map.of(
			"IsReflexive", "Is the relation R reflexive over S?",
			"IsIrreflexive", "Is the relation R irreflexive over set S?",
			"IsSymmetric", "Is the relation R symmetric over set S?",
			"IsAsymmetric", "Is the relation R asymmetric over set S?",
			"IsTransitive", "Is the relation R transitive over set S?",
			"TransitiveClosure", "Compute the transitive closure of relation R over set S",
			"ReflexiveTransitiveClosure", "Compute the reflexive transitive closure of relation R over set S",
			"IsConnected", "Is the relation R connected over set S"
		));

		for (int i = 0; i < preCommentsNodes.getLength(); i++) {
			Element preComment = (Element) preCommentsNodes.item(i);
			String commentText = preComment.getTextContent();

			// Pre-comments should not be empty
			Assert.assertFalse("Pre-comment should not be empty", commentText.trim().isEmpty());

			Element parent = (Element) preComment.getParentNode();
			NodeList uniqueNames = parent.getElementsByTagName("uniquename");
			if (uniqueNames.getLength() == 0)
				continue;

			String opName = uniqueNames.item(0).getTextContent().trim();

			String expected = expectedUncommentedContent.get(opName);
			if (expected != null && commentText.contains(expected)) {
				// Found this operator's uncommented content, remove it from the map
				expectedUncommentedContent.remove(opName);
			}
		}

		// Assert that all expected uncommented content was found
		Assert.assertTrue("Missing expected uncommented content for: " + expectedUncommentedContent.keySet(),
				expectedUncommentedContent.isEmpty());
	}
}
