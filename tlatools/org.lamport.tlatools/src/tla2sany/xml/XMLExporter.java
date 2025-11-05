
// Copyright (c) 2013 INRIA-MSR.  All rights reserved.

package tla2sany.xml;

/**
 * a tool for exporting the loaded modules to XML format
 */

import java.io.PrintStream;
import java.net.URL;
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

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.xml.sax.SAXException;

import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.output.LogLevel;
import tla2sany.output.SanyOutput;
import tla2sany.output.SimpleSanyOutput;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefOrDeclNode;
import tla2sany.semantic.SemanticNode;
import util.FileUtil;
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

  public static void main(String... args) throws XMLExportingException {
    System.exit(run(args));
  }

  static int run(String... args) throws XMLExportingException {
    try {
      moduleToXML(args);
      return 0;
    } catch (IllegalArgumentException e) {
      ToolIO.err.println("ERROR: " + e.getMessage());
      printUsage(ToolIO.err);
      return 1;
    }
  }

  static void moduleToXML(String... args) throws XMLExportingException {

    if (args.length < 1) throw new IllegalArgumentException("at least one .tla file must be given");
    LinkedList<String> pathsLs = new LinkedList<>();

    boolean offline_mode = false;
    boolean pretty_print = true;
    boolean restricted = false;
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
      } else if ("-I".equals(args[i])) {
        i++;
        if (i > args.length - 2)
          throw new IllegalArgumentException("the -I flag must be followed by a directory and at least one .tla file");
        pathsLs.addLast(args[i]);
        lastarg = i;
      }
    }

    lastarg++;

    String[] paths = new String[pathsLs.size()];
    for (int i = 0; i < paths.length; i++) paths[i] = (String) pathsLs.get(i);

    if (args.length - lastarg != 1)
      throw new IllegalArgumentException("Only one TLA file to check allowed!");

    if (args[args.length - 1].equals("-help")) {
        printUsage(ToolIO.out);
        return;
    }

    String tla_name = args[lastarg++];

    FilenameToStream fts = new SimpleFilenameToStream(paths);

    SpecObj spec = new SpecObj(tla_name, fts);

    // Get next file name from command line; then parse,
    // semantically analyze, and level check the spec started in
    // file Filename leaving the result (normally) in Specification
    // spec.
    // check if file exists
    //ToolIO.out.println("Processing: "+tlas[i]+"\n"+(tlas[i] == null));
    if (FileUtil.createNamedInputStream(tla_name, spec.getResolver()) != null) {
      try {
        SanyOutput out = new SimpleSanyOutput(ToolIO.err, LogLevel.ERROR);
        SANY.frontEndMain(spec, tla_name, out);
        if (spec.getExternalModuleTable() == null)
          throw new XMLExportingException("spec " + spec.getName() + " is malformed - does not have an external module table", null);
        if (spec.getExternalModuleTable().getRootModule() == null)
          throw new XMLExportingException("spec " + spec.getName() + " is malformed - does not have a root module", null);
      } catch (FrontEndException fe) {
        // For debugging
        fe.printStackTrace();
        ToolIO.err.println(fe);
        return;
      }
    } else {
      throw new IllegalArgumentException("Cannot find the specified file " + tla_name + ".");
    }


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

      //Export all the external modules
      ExternalModuleTable table = spec.getExternalModuleTable();
      //Element e = table.getRootModule().exportDefinition(doc,context);
      //rootElement.appendChild(e);
      
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
			ModuleNode[] externalModules = table.getModuleNodes();
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
            ToolIO.err.println("ERROR: Unable to find sany.xsd schema file that is expected to be embedded in the jar.");
            System.exit(1);
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
      StreamResult result = new StreamResult(ToolIO.out);

      transformer.transform(source, result);
    } catch (ParserConfigurationException pce) {
      throw new XMLExportingException("failed to write XML", pce);
    } catch (TransformerException tfe) {
      throw new XMLExportingException("failed to write XML", tfe);
    } catch (SAXException se) {
      throw new XMLExportingException("failed to validate XML", se);
    }

  }

  static void insertRootName(Document doc, Element rootElement, SpecObj spec) {
    Element el = doc.createElement("RootModule");
    el.appendChild(doc.createTextNode(spec.getName()));
    rootElement.insertBefore(el, rootElement.getFirstChild());
  }
}
