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
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
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
			// Strip to normalize indentation whitespace that some XML serializers
			// (notably Java 11's Transformer with INDENT=yes) add around CDATA sections.
			String commentText = preComment.getTextContent().trim();

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

	/**
	 * Runs the XMLExporter on the given module, asserts that it succeeded
	 * quietly, and returns the parsed, schema-validated output document.
	 */
	private Document export(final String moduleName) throws Exception {
		int exitCode = XMLExporter.run("-I", BASE_PATH, BASE_PATH + moduleName + ".tla");
		Assert.assertEquals("XMLExporter should exit with code 0", 0, exitCode);
		Assert.assertTrue("No errors should be written to stderr", this.errStream.toString().trim().isEmpty());

		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		factory.setNamespaceAware(true);
		DocumentBuilder builder = factory.newDocumentBuilder();
		Document doc = builder.parse(new InputSource(new StringReader(this.outStream.toString())));

		SchemaFactory schemaFactory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
		URL schemaFile = XMLExporter.class.getResource("sany.xsd");
		Assert.assertNotNull("sany.xsd schema file should be found", schemaFile);
		Schema schema = schemaFactory.newSchema(schemaFile);
		Validator validator = schema.newValidator();
		validator.validate(new DOMSource(doc));

		return doc;
	}

	/**
	 * Maps each module in the context table to the names of the modules nested
	 * in its body, in the order in which they are exported.
	 */
	private Map<String, List<String>> nestedModules(final Document doc) {
		Map<String, String> uidToName = new HashMap<>();
		Map<String, List<String>> nestedUids = new LinkedHashMap<>();
		NodeList entries = doc.getElementsByTagName("entry");
		for (int i = 0; i < entries.getLength(); i++) {
			Element entry = (Element) entries.item(i);
			NodeList moduleNodes = entry.getElementsByTagName("ModuleNode");
			if (moduleNodes.getLength() == 0) {
				continue;
			}
			Element module = (Element) moduleNodes.item(0);
			String name = module.getElementsByTagName("uniquename").item(0).getTextContent().trim();
			uidToName.put(entry.getElementsByTagName("UID").item(0).getTextContent().trim(), name);

			List<String> children = new ArrayList<>();
			NodeList refs = module.getElementsByTagName("ModuleNodeRef");
			for (int j = 0; j < refs.getLength(); j++) {
				Element ref = (Element) refs.item(j);
				children.add(ref.getElementsByTagName("UID").item(0).getTextContent().trim());
			}
			nestedUids.put(name, children);
		}

		Map<String, List<String>> result = new LinkedHashMap<>();
		for (Map.Entry<String, List<String>> entry : nestedUids.entrySet()) {
			List<String> names = new ArrayList<>();
			for (String uid : entry.getValue()) {
				names.add(uidToName.getOrDefault(uid, "<unresolvable UID " + uid + ">"));
			}
			result.put(entry.getKey(), names);
		}
		return result;
	}

	/** The names of the modules listed at the top level of the document. */
	private List<String> topLevelModules(final Document doc) {
		Map<String, String> uidToName = new HashMap<>();
		NodeList entries = doc.getElementsByTagName("entry");
		for (int i = 0; i < entries.getLength(); i++) {
			Element entry = (Element) entries.item(i);
			NodeList moduleNodes = entry.getElementsByTagName("ModuleNode");
			if (moduleNodes.getLength() > 0) {
				uidToName.put(entry.getElementsByTagName("UID").item(0).getTextContent().trim(),
						((Element) moduleNodes.item(0)).getElementsByTagName("uniquename").item(0).getTextContent()
								.trim());
			}
		}

		List<String> result = new ArrayList<>();
		NodeList refs = doc.getDocumentElement().getChildNodes();
		for (int i = 0; i < refs.getLength(); i++) {
			if (refs.item(i) instanceof Element && "ModuleNodeRef".equals(refs.item(i).getNodeName())) {
				Element ref = (Element) refs.item(i);
				result.add(uidToName.get(ref.getElementsByTagName("UID").item(0).getTextContent().trim()));
			}
		}
		return result;
	}

	@Test
	public void testNestedModuleIsChildOfEnclosingModule() throws Exception {
		// NestedModuleXml.tla nests "Instantiated" and "Standalone" in its body, and
		// "Standalone" in turn nests "Innermost".
		Document doc = this.export("NestedModuleXml");
		Map<String, List<String>> nested = this.nestedModules(doc);

		Assert.assertEquals("Modules nested in NestedModuleXml, in source order",
				List.of("Instantiated", "Standalone"), nested.get("NestedModuleXml"));
		Assert.assertEquals("Nesting is preserved to arbitrary depth",
				List.of("Innermost"), nested.get("Standalone"));

		// "Standalone" is never instantiated or otherwise referenced, so nothing but
		// the containment relationship makes it reachable.
		Assert.assertTrue("Unreferenced nested module should still be exported", nested.containsKey("Standalone"));

		// A nested module is a unit of its enclosing module, not a module of the
		// specification.
		Assert.assertEquals("Only outer modules are listed at the top level",
				List.of("Naturals", "NestedModuleXml"), this.topLevelModules(doc));

		this.assertEachModuleReachableOnce(doc);
	}

	@Test
	public void testNestedModuleIsNotInheritedThroughExtends() throws Exception {
		// "Sub" is nested in the body of NestedModuleXmlBase, which
		// NestedModuleXmlExtender extends both directly and from "Borrower", a
		// module nested in its body. Extending a module does not nest that module's
		// modules in the extender, even though SANY's Context merge makes "Sub"
		// visible in both places by name; see ModuleNode#getSymbolElement.
		Document doc = this.export("NestedModuleXmlExtender");
		Map<String, List<String>> nested = this.nestedModules(doc);

		Assert.assertEquals("Sub is a unit of the module whose body contains it",
				List.of("Sub"), nested.get("NestedModuleXmlBase"));
		Assert.assertEquals("An extended module's modules are not units of the extender",
				List.of("Borrower"), nested.get("NestedModuleXmlExtender"));
		Assert.assertEquals("...nor of a module nested in the extender",
				List.of(), nested.get("Borrower"));

		this.assertEachModuleReachableOnce(doc);
	}

	/**
	 * Asserts that every module in the context table is reachable exactly once,
	 * either from the top level of the document or as a unit of exactly one
	 * enclosing module.
	 */
	private void assertEachModuleReachableOnce(final Document doc) {
		List<String> reachable = new ArrayList<>(this.topLevelModules(doc));
		this.nestedModules(doc).values().forEach(reachable::addAll);
		Assert.assertEquals("No module is reachable twice", Set.copyOf(reachable).size(), reachable.size());
		Assert.assertEquals("Every exported module is reachable", this.nestedModules(doc).keySet(),
				Set.copyOf(reachable));
	}

	@Test
	public void testLetInstanceOfEmptyModuleExportsModuleInstanceRef() throws Exception {
		Document doc = this.export("Github1417");

		Assert.assertEquals("An instancee without definitions leaves only the instance to export",
				List.of("ModuleInstanceKindRef"), this.letInOpDefKinds(doc, "op"));

		// Schema validation does not check that a reference resolves.
		Element instance = this.referent(doc, this.letInOpDefs(doc, "op").get(0));
		Assert.assertEquals("The exported reference resolves to a module instance", "ModuleInstanceKind",
				instance.getNodeName());
		Assert.assertEquals("...under the name the LET binds it to", "M", uniqueName(instance));
	}

	@Test
	public void testLetInstanceWithNothingToInlineExportsModuleInstanceRef() throws Exception {
		// A module that defines nothing but LOCAL definitions instantiates none.
		Document doc = this.export("Github1417Variants");

		Assert.assertEquals("A LOCAL definition of the instancee is not inlined",
				List.of("ModuleInstanceKindRef"), this.letInOpDefKinds(doc, "opLocal"));
		Assert.assertEquals("...leaving the instance as the only export", "Local",
				uniqueName(this.referent(doc, this.letInOpDefs(doc, "opLocal").get(0))));

		Assert.assertEquals("A parameterized module definition exports its instance too",
				List.of("ModuleInstanceKindRef"), this.letInOpDefKinds(doc, "opParam"));
		Assert.assertEquals("...under the name the LET binds it to", "Param",
				uniqueName(this.referent(doc, this.letInOpDefs(doc, "opParam").get(0))));
	}

	@Test
	public void testLetInstanceInlinesDefinitionsOfInstancee() throws Exception {
		Document doc = this.export("Github1417Inlined");

		Assert.assertEquals("An operator of the instancee is inlined as Ops!foo", "Ops!foo", uniqueName(
				this.referent(doc, this.letInOpDef(doc, "opOps", "UserDefinedOpKindRef"))));
		Assert.assertEquals("A named theorem of the instancee is inlined as Thms!Thm", "Thms!Thm", uniqueName(
				this.referent(doc, this.letInOpDef(doc, "opThm", "TheoremDefRef"))));
		Assert.assertEquals("A named assumption of the instancee is inlined as Thms!Asm", "Thms!Asm", uniqueName(
				this.referent(doc, this.letInOpDef(doc, "opThm", "AssumeDefRef"))));
	}

	@Test
	public void testLetExportsEachModuleDefinitionIndependently() throws Exception {
		Document doc = this.export("Github1417Variants");

		Assert.assertEquals("Every module definition contributes what it instantiates, then itself",
				List.of("Both!foo", "Both", "Nothing"), this.letInOpDefNames(doc, "opMixed"));
	}

	@Test
	public void testLetAlwaysExportsModuleInstanceRef() throws Exception {
		// opDefs is the only place an instance can appear: unlike ModuleNode,
		// LetInNode does not export the InstanceNodes of its module definitions.
		Document doc = this.export("Github1417Inlined");

		Assert.assertEquals("An instance whose definitions were inlined is exported too",
				List.of("Ops!foo", "Ops"), this.letInOpDefNames(doc, "opOps"));

		// Inlined definitions come in the order of a Hashtable enumeration.
		List<String> inlined = this.letInOpDefNames(doc, "opThm");
		Assert.assertEquals("...as is one that contributed a theorem and an assumption",
				Set.of("Thms!Thm", "Thms!Asm"), Set.copyOf(inlined.subList(0, inlined.size() - 1)));
		Assert.assertEquals("...which the instance follows", "Thms", inlined.get(inlined.size() - 1));
	}

	@Test
	public void testTopLevelInstanceOfEmptyModuleExportsInstanceNode() throws Exception {
		// A module's list of units may legitimately be empty, so #1417 spared it.
		Document doc = this.export("Github1417TopLevel");

		NodeList instances = doc.getElementsByTagName("InstanceNode");
		Assert.assertEquals("The module-level instance is exported", 1, instances.getLength());

		Element instance = (Element) instances.item(0);
		Assert.assertEquals("...under the name it is defined as", "M", uniqueName(instance));
		Assert.assertEquals("...naming the module it instantiates", "Github1417Empty",
				child(instance, "module").getTextContent().trim());
	}

	/**
	 * The references exported in the opDefs list of the LET-IN that makes up the
	 * body of the given operator, in export order.
	 */
	private List<Element> letInOpDefs(final Document doc, final String opName) {
		Element definition = null;
		NodeList definitions = doc.getElementsByTagName("UserDefinedOpKind");
		for (int i = 0; i < definitions.getLength(); i++) {
			Element candidate = (Element) definitions.item(i);
			if (opName.equals(uniqueName(candidate))) {
				definition = candidate;
				break;
			}
		}
		Assert.assertNotNull("Operator " + opName + " should be exported", definition);

		NodeList letIns = definition.getElementsByTagName("LetInNode");
		Assert.assertEquals("Operator " + opName + " should be defined by a single LET-IN", 1, letIns.getLength());
		return childElements(child((Element) letIns.item(0), "opDefs"));
	}

	/** Those of {@link #letInOpDefs(Document, String)} with the given element name. */
	private List<Element> letInOpDefs(final Document doc, final String opName, final String kind) {
		List<Element> refs = new ArrayList<>();
		for (Element opDef : this.letInOpDefs(doc, opName)) {
			if (kind.equals(opDef.getNodeName())) {
				refs.add(opDef);
			}
		}
		return refs;
	}

	/** The only one of {@link #letInOpDefs(Document, String)} with the given element name. */
	private Element letInOpDef(final Document doc, final String opName, final String kind) {
		List<Element> refs = this.letInOpDefs(doc, opName, kind);
		Assert.assertEquals("The LET-IN of " + opName + " should export exactly one " + kind, 1, refs.size());
		return refs.get(0);
	}

	/** The element names of {@link #letInOpDefs(Document, String)}. */
	private List<String> letInOpDefKinds(final Document doc, final String opName) {
		List<String> kinds = new ArrayList<>();
		for (Element opDef : this.letInOpDefs(doc, opName)) {
			kinds.add(opDef.getNodeName());
		}
		return kinds;
	}

	/** The names of the nodes that {@link #letInOpDefs(Document, String)} resolve to. */
	private List<String> letInOpDefNames(final Document doc, final String opName) {
		List<String> names = new ArrayList<>();
		for (Element opDef : this.letInOpDefs(doc, opName)) {
			names.add(uniqueName(this.referent(doc, opDef)));
		}
		return names;
	}

	/** The node in the context table that the given reference points at. */
	private Element referent(final Document doc, final Element ref) {
		String uid = child(ref, "UID").getTextContent().trim();
		NodeList entries = doc.getElementsByTagName("entry");
		for (int i = 0; i < entries.getLength(); i++) {
			// The schema defines an entry as a UID followed by the node it names.
			List<Element> entry = childElements((Element) entries.item(i));
			if (uid.equals(entry.get(0).getTextContent().trim())) {
				return entry.get(1);
			}
		}
		Assert.fail(ref.getNodeName() + " should resolve to a context table entry, but UID " + uid + " is unknown");
		return null;
	}

	/** The uniquename of the given node, or null if it does not have one. */
	private static String uniqueName(final Element node) {
		for (Element child : childElements(node)) {
			if ("uniquename".equals(child.getNodeName())) {
				return child.getTextContent().trim();
			}
		}
		return null;
	}

	/** The child elements of the given element, skipping the whitespace between them. */
	private static List<Element> childElements(final Element parent) {
		List<Element> elements = new ArrayList<>();
		NodeList children = parent.getChildNodes();
		for (int i = 0; i < children.getLength(); i++) {
			if (children.item(i) instanceof Element) {
				elements.add((Element) children.item(i));
			}
		}
		return elements;
	}

	/** The only child element of the given element with the given name. */
	private static Element child(final Element parent, final String name) {
		List<Element> matches = new ArrayList<>();
		for (Element child : childElements(parent)) {
			if (name.equals(child.getNodeName())) {
				matches.add(child);
			}
		}
		Assert.assertEquals(parent.getNodeName() + " should have exactly one " + name + " child", 1, matches.size());
		return matches.get(0);
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

	@Test
	public void testLetInstanceExportsInstantiatedTheoremAndAssumption() throws Exception {
		// Only a LET exports an instantiated theorem definition as a reference.
		Document doc = this.export("LetInstanceThmXml");

		NodeList letIns = doc.getElementsByTagName("LetInNode");
		Assert.assertEquals("The LET should be exported", 1, letIns.getLength());

		Element letIn = (Element) letIns.item(0);
		Assert.assertEquals("The instantiated theorem is exported as a reference", 1,
				letIn.getElementsByTagName("TheoremDefRef").getLength());
		Assert.assertEquals("...and so is the instantiated assumption", 1,
				letIn.getElementsByTagName("AssumeDefRef").getLength());
	}
	@Test
	public void testRecursiveSectionGroupsJointDeclaration() throws Exception {
		// f and g are declared together (RECURSIVE f(_), g(_)); h is declared by a
		// separate RECURSIVE statement; nonRecursive isn't recursive at all.
		Document doc = this.export("RecursiveSectionXml");

		Element f = this.userDefinedOpKind(doc, "f");
		Element g = this.userDefinedOpKind(doc, "g");
		Element h = this.userDefinedOpKind(doc, "h");
		Element nonRecursive = this.userDefinedOpKind(doc, "nonRecursive");

		String fSection = this.recursiveSection(f);
		String gSection = this.recursiveSection(g);
		String hSection = this.recursiveSection(h);

		Assert.assertNotNull("A jointly-declared operator reports a recursiveSection", fSection);
		Assert.assertEquals("f and g were declared by the same RECURSIVE statement", fSection, gSection);
		Assert.assertNotNull("A singly-declared recursive operator reports a recursiveSection too", hSection);
		Assert.assertNotEquals("h was declared by a separate RECURSIVE statement", fSection, hSection);
		Assert.assertNull("A non-recursive operator has no recursiveSection", this.recursiveSection(nonRecursive));
	}

	/** The UserDefinedOpKind element exported for the operator of the given name. */
	private Element userDefinedOpKind(final Document doc, final String opName) {
		NodeList definitions = doc.getElementsByTagName("UserDefinedOpKind");
		for (int i = 0; i < definitions.getLength(); i++) {
			Element candidate = (Element) definitions.item(i);
			if (opName.equals(uniqueName(candidate))) {
				return candidate;
			}
		}
		Assert.fail("Operator " + opName + " should be exported");
		return null;
	}

	/** The text of a UserDefinedOpKind's recursiveSection child, or null if it has none. */
	private String recursiveSection(final Element userDefinedOpKind) {
		NodeList sections = userDefinedOpKind.getElementsByTagName("recursiveSection");
		if (sections.getLength() == 0) {
			return null;
		}
		return sections.item(0).getTextContent().trim();

	@Test
	public void testUseHideDefsExportsModuleReference() throws Exception {
		// Regression test: a USE/HIDE block's defs list is exported and validated
		// identically to its facts list, but the schema's defs choice previously
		// omitted ModuleNodeRef even though facts allowed it, so HIDE DEFS MODULE M
		// failed schema validation despite being valid TLA+ and already exported
		// correctly.
		Document doc = this.export("UseHideModuleDefsXml");

		NodeList useOrHideNodes = doc.getElementsByTagName("UseOrHideNode");
		Assert.assertEquals("The HIDE statement should be exported", 1, useOrHideNodes.getLength());

		List<Element> defs = childElements(child((Element) useOrHideNodes.item(0), "defs"));
		Assert.assertEquals("MODULE UseHideModuleDefsXmlSub and x should both be exported as defs", 2, defs.size());

		int moduleRefs = 0;
		for (Element def : defs) {
			if ("ModuleNodeRef".equals(def.getNodeName())) {
				moduleRefs++;
			}
		}
		Assert.assertEquals("The MODULE reference should be exported as ModuleNodeRef", 1, moduleRefs);
	}
}
