
// Copyright (c) 2013 INRIA-MSR.  All rights reserved.

package tla2sany.xml;

/**
 * a tool for exporting the loaded modules to XML format
 */

import java.io.ByteArrayOutputStream;
import java.io.FileNotFoundException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.function.BiPredicate;

import javax.xml.XMLConstants;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;
import javax.xml.validation.Validator;

import org.w3c.dom.CDATASection;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.drivers.SanyExitCode;
import tla2sany.drivers.SanySettings;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.output.LogLevel;
import tla2sany.output.SanyOutput;
import tla2sany.output.SimpleSanyOutput;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefOrDeclNode;
import tla2sany.semantic.SemanticNode;
import util.FilenameToStream;
import util.SimpleFilenameToStream;
import util.ToolIO;
import util.UsageGenerator;

public class XMLExporter {

  /**
   * Construct & output the usage text for this program.
   *
   * @param out The output stream to which to print the usage.
   */
  static final void printUsage(final PrintStream out) {
    List<List<UsageGenerator.Argument>> variants = new ArrayList<List<UsageGenerator.Argument>>();
    List<UsageGenerator.Argument> args = new ArrayList<UsageGenerator.Argument>();
    args.add(new UsageGenerator.Argument(
        "-o", "Offline mode; skip XML schema validation step.", true));
    args.add(new UsageGenerator.Argument(
        "-t", "Terse; format XML output without tabs or newlines.", true));
	args.add(new UsageGenerator.Argument("-r",
			"Restrict mode; include only declarations and definitions of the specified module, excluding extended or instantiated modules.",
			true));
	args.add(new UsageGenerator.Argument("-u",
			"Uncomment; process boxed comments and single-line comments (\\*) in pre-comments to extract their content.",
			true));
    args.add(new UsageGenerator.Argument(
        "-I", "Include; use given directory path to resolve module dependencies.", true));
    args.add(new UsageGenerator.Argument(
        "-help", "Print this usage information.", true));
    args.add(new UsageGenerator.Argument(
        "FILE", "The TLA+ module to parse.", false));
    variants.add(args);
    List<String> tips = new ArrayList<String>();
    tips.add("Only one root TLA+ file can be parsed per run.");
    tips.add("Multiple directory search paths can be given by providing multiple -I arguments.");
    tips.add("XML schema validation does not require network access.");
    UsageGenerator.displayUsage(
        out,
        XMLExporter.class.getCanonicalName(),
        SANY.version,
        "Emit SANY's parse tree as XML",
        "Given a TLA+ file, parse that file with SANY then translate the module's " +
        "semantic parse tree to XML, including all the modules depended on. The " +
        "XML is printed to stdout and its output format is given by an XML Schema " +
        "file (.xsd) found at https://proofs.tlapl.us/doc/web/sany.xsd.",
        variants,
        tips,
        ' '
      );
  }

  /**
   * Directly calls {@link XMLExporter#run(String...)} then calls
   * {@link System#exit(int)} with the code that it returns. Possible return
   * codes can be found in the {@link XMLExporterExitCode} class.
   *
   * @param args The list of command line-arguments.
   */
  public static void main(final String... args) {
    System.exit(run(args));
  }

  /**
   * Runs the XML Exporter, printing the XML output to standard output. If
   * any errors occur, the human-readable error message will be printed to
   * standard error and a nonzero exit code will be returned. The meaning of
   * error codes can be found in the {@link XMLExporterExitCode} class.
   *
   * @param args The list of command-line arguments.
   * @return An error code; 0 if successful.
   */
  public static int run(final String... args) {
    try {
      moduleToXML(args);
      return XMLExporterExitCode.OK.code();
    } catch (XMLExportingException e) {
      final XMLExporterExitCode error = e.code();
      if (error == XMLExporterExitCode.ARGS_PARSING_FAILURE) {
        ToolIO.err.println("ERROR: " + e.getMessage());
        printUsage(ToolIO.err);
        return error.code();
      } else {
        ToolIO.err.println(e.toString());
        if (error.isBug()) {
          ToolIO.err.println(
            "This is likely a bug in the XML Exporter; please report to " +
            "https://github.com/tlaplus/tlaplus/issues"
          );
        }

        return error.code();
      }
    }
  }

  /**
   * Parses the given command line arguments then converts the specified TLA+
   * spec to XML, output to standard output. Will throw a {@link XMLExportingException}
   * on error. On success, simply returns without throwing an exception.
   *
   * @param args The list of command-line arguments.
   * @throws XMLExportingException On error, such as spec parsing failure.
   */
  static void moduleToXML(String... args) throws XMLExportingException {

    if (args.length < 1) {
      throw new XMLExportingException(
          XMLExporterExitCode.ARGS_PARSING_FAILURE,
          "at least one .tla file must be given", null);
    }
    LinkedList<String> pathsLs = new LinkedList<>();

    boolean offline_mode = false;
    boolean pretty_print = true;
    boolean restricted = false;
    boolean uncomment = false;
    int lastarg = -1; // lastarg will be incremented, initialize at -1
    for (int i = 0; i < args.length - 1; i++) {
      if ("-o".equals(args[i])) {
        offline_mode = true;
        lastarg = i;
      } else if ("-t".equals(args[i])) {
        pretty_print = false;
        lastarg = i;
      } else if ("-r".equals(args[i])) {
          restricted = true;
          lastarg = i;
      } else if ("-u".equals(args[i])) {
          uncomment = true;
          lastarg = i;
      } else if ("-I".equals(args[i])) {
        i++;
        if (i > args.length - 2)
          throw new XMLExportingException(
              XMLExporterExitCode.ARGS_PARSING_FAILURE,
              "the -I flag must be followed by a directory and at least one .tla file", null);
        pathsLs.addLast(args[i]);
        lastarg = i;
      }
    }

    lastarg++;

    String[] paths = new String[pathsLs.size()];
    for (int i = 0; i < paths.length; i++) paths[i] = (String) pathsLs.get(i);

    if (args.length - lastarg != 1)
      throw new XMLExportingException(
          XMLExporterExitCode.ARGS_PARSING_FAILURE,
          "Only one TLA file to check allowed!", null);

    if (args[args.length - 1].equals("-help")) {
        printUsage(ToolIO.out);
        return;
    }

    String tla_name = args[lastarg++];

    final ExternalModuleTable spec = XMLExporter.parseSpec(tla_name, paths);
    XMLExporter.specToXMLStream(
        spec,
        restricted,
        uncomment,
        pretty_print,
        offline_mode,
        ToolIO.out
      );
  }

  /**
   * Parses the TLA+ spec with the given path and import directories. Throws
   * an exception on parse failure.
   *
   * @param specPath The path to the TLA+ spec.
   * @param includeDirs A list of directories in which to search for imports.
   * @return A {@link ExternalModuleTable} of all parsed modules.
   * @throws XMLExportingException On parse failure.
   */
  static ExternalModuleTable parseSpec(
      final String specPath,
      final String... includeDirs
  ) throws XMLExportingException {
    FilenameToStream fts = new SimpleFilenameToStream(includeDirs);

    SpecObj spec = new SpecObj(specPath, fts);

    try {
      final SanyOutput out = new SimpleSanyOutput(ToolIO.err, LogLevel.ERROR);
      final SanySettings settings = SanySettings.validAstSettings();
      if (SanyExitCode.OK != SANY.parse(spec, specPath, out, settings)) {
        throw new XMLExportingException(
            XMLExporterExitCode.SPEC_PARSING_FAILURE,
            "Failed to parse module.", null);
      }

      return spec.getExternalModuleTable();
    } catch (FrontEndException fe) {
      throw new XMLExportingException(
          XMLExporterExitCode.SPEC_PARSING_FAILURE,
          "Failed to parse module.", fe);
    }
  }

  /**
   * Calls {@link XMLExporter#specToXMLStream} but captures its output in a
   * {@link ByteArrayOutputStream} instance to convert to a string, which is
   * returned.
   *
   * @param spec The table of TLA+ specs to convert.
   * @param restricted Only export the root TLA+ module.
   * @param uncomment Process operator pre-comments to remove '(*' and '*)'.
   * @param prettyPrint XML output will have line breaks and indentation.
   * @param offlineMode Skip schema validation (not recommended).
   * @return A string representation of the XML output.
   * @throws XMLExportingException If error occurred during XML conversion.
   */
  static String specToXMLString(
      final ExternalModuleTable spec,
      final boolean restricted,
      final boolean uncomment,
      final boolean prettyPrint,
      final boolean offlineMode
  ) throws XMLExportingException {
    final ByteArrayOutputStream output = new ByteArrayOutputStream();
    specToXMLStream(spec, restricted, uncomment, prettyPrint, offlineMode, output);
    return output.toString(StandardCharsets.UTF_8);
  }

  /**
   * Converts the given set of TLA+ specs to XML and then outputs the XML to
   * the given {@link OutputStream} instance.
   *
   * @param spec The table of TLA+ specs to convert.
   * @param restricted Only export the root TLA+ module.
   * @param uncomment Process operator pre-comments to remove '(*' and '*)'.
   * @param pretty_print XML output will have line breaks and indentation.
   * @param offline_mode Skip schema validation (not recommended).
   * @param output The stream to which to output the XML.
   * @throws XMLExportingException If error occurred during XML conversion.
   */
  static void specToXMLStream(
      final ExternalModuleTable spec,
      final boolean restricted,
      final boolean uncomment,
      final boolean pretty_print,
      final boolean offline_mode,
      final OutputStream output
  ) throws XMLExportingException {
    try {

      DocumentBuilderFactory docFactory =
              DocumentBuilderFactory.newInstance();

      // write XML
      DocumentBuilder docBuilder = docFactory.newDocumentBuilder();

      // root elements
      Document doc = docBuilder.newDocument();
      Element rootElement = doc.createElement("modules");
      doc.appendChild(rootElement);
      // Create symbol context. It will be filled by all symbol references during module export.
      SymbolContext context = new SymbolContext();

		if (restricted) {
			final BiPredicate<SemanticNode, SemanticNode> filter = (s1, s2) -> {
				if (s1 instanceof OpDefOrDeclNode && s2 instanceof ModuleNode) {
					final OpDefOrDeclNode oddn = (OpDefOrDeclNode) s1;
					return s2.equals(oddn.getOriginallyDefinedInModuleNode());
				}
				return true;
			};
			Element ext_e = spec.getRootModule().export(doc, context, filter);
			rootElement.appendChild(ext_e);
		} else {
			ModuleNode[] externalModules = spec.getModuleNodes();
			for (int j = 0; j < externalModules.length; j++) {
				// Element ext_e = externalModules[j].exportDefinition(doc, context);
				Element ext_e = externalModules[j].export(doc, context);
				rootElement.appendChild(ext_e);
			}
		}

      // Insert the symbol table into the beginning of the XML DOM
      rootElement.insertBefore(context.getContextElement(doc), rootElement.getFirstChild());

      //Insert name of root module
      insertRootName(doc, rootElement, spec);

      if (uncomment) {
			// Instead of traversing all XML nodes, it would be more efficient to uncomment
			// pre-comments directly within SANY's OpDefNode#getSymbolElement during the AST
			// traversal that produces the XML. Moreover, since SemanticNode#getPreComments
			// already returns an array of strings, the subsequent string-splitting
			// operations are unnecessary. Unfortunately, I don't have time to refactor
			// XMLExportable#export to accept a (generic) visitor capable of mapping,
			// mutating, or transforming AST elements prior to their conversion into XML
			// nodes (see https://github.com/tlaplus/tlaplus/issues/1236)
    	  NodeList nodes = doc.getElementsByTagName("pre-comments");
          for (int i = 0; i < nodes.getLength(); i++) {
              NodeList children = ((Element) nodes.item(i)).getChildNodes();
              for (int j = 0; j < children.getLength(); j++) {
                  Node child = children.item(j);
                  if (child.getNodeType() == Node.CDATA_SECTION_NODE) {
						((CDATASection) child).setData(SyntaxTreeNode.unboxBackslashStarComment(
								SyntaxTreeNode.unboxComment(((CDATASection) child).getData())));
	              }
              }
          }
      }

      //Create XML file
      TransformerFactory transformerFactory = TransformerFactory.newInstance();
      Transformer transformer = transformerFactory.newTransformer();
      if (pretty_print) {
        transformer.setOutputProperty(OutputKeys.INDENT, "yes");
        transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "2");
      }
      DOMSource source = new DOMSource(doc);

      // validate the file, do not fail if there is a URL connection error
      if (!offline_mode) { //skip validation in offline mode
        try {
          SchemaFactory factory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
          URL schemaFile = XMLExporter.class.getResource("sany.xsd");
          if (null == schemaFile) {
            throw new XMLExportingException(
                XMLExporterExitCode.XML_CANNOT_FIND_EMBEDDED_SCHEMA_FILE,
                "Unable to find sany.xsd schema file that is expected to be embedded in the jar.",
                new FileNotFoundException("Resource sany.xsd not found in classpath"));
          }
          Schema schema = factory.newSchema(schemaFile);
          // create a Validator instance, which can be used to validate an instance document
          Validator validator = schema.newValidator();
          //validate the DOM tree
          validator.validate(source);
        } catch (java.io.IOException ioe) {
          // do nothing if there is no internet connection
          // but fail for other errors
        }
          /*catch (org.xml.sax.SAXParseException spe) {
            // do nothing if there is no internet connection
            // but fail for other errors
          }*/
      }

      StreamResult result = new StreamResult(output);
      transformer.transform(source, result);
    } catch (ParserConfigurationException pce) {
      throw new XMLExportingException(XMLExporterExitCode.XML_CONFIGURATION_FAILURE, "Failed to write XML", pce);
    } catch (TransformerException tfe) {
      throw new XMLExportingException(XMLExporterExitCode.XML_TRANSFORMATION_FAILURE, "Failed to transform XML", tfe);
    } catch (SAXException se) {
      throw new XMLExportingException(XMLExporterExitCode.XML_SCHEMA_VALIDATION_FAILURE, "Failed to validate XML", se);
    }
  }

  static void insertRootName(Document doc, Element rootElement, final ExternalModuleTable spec) {
    Element el = doc.createElement("RootModule");
    el.appendChild(doc.createTextNode(spec.getRootModule().getName().toString()));
    rootElement.insertBefore(el, rootElement.getFirstChild());
  }
}
