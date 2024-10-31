
// Copyright (c) 2013 INRIA-MSR.  All rights reserved.

package tla2sany.xml;

import java.io.ByteArrayOutputStream;

/**
 * a tool for exporting the loaded modules to XML format
 */

import java.io.PrintStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;

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
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.ModuleNode;
import util.FileUtil;
import util.FilenameToStream;
import util.SimpleFilenameToStream;
import util.ToolIO;

public class XMLExporter {

  /**
   * CLI help text listing various options.
   */
  private static final String HELP_TEXT =
    "SANY XML Exporter\n" +
    "Usage:\n\n" +
    "  java tla2sany.xml.XMLExporter [-o|-p] [-I <dir_path>]* <input_file>.tla\n\n" +
    "Options:\n" +
    "  -o: Offline mode; skip XML schema validation step.\n" +
    "  -p: Pretty-print; format XML output to be read by humans.\n" +
    "  -I: Include; use given directory path to resolve module dependencies.\n" +
    "  -h: Help; print this help text.\n";

  /**
   * The main entry-point to the XML exporter program. Parses the command-
   * line args then calls the main run function. Terminates with 0 exit code
   * if successful, 1 on failure.
   *
   * @param args The command-line args.
   */
  public static final void main(String[] args) {
    try {
      RunOptions options = parseArgs(args);
      if (null == options) {
        ToolIO.out.println(HELP_TEXT);
      } else {
        boolean success = run(options.OfflineMode, options.PrettyPrint, options.Include, options.TlaFile);
        System.exit(success ? 0 : 1);
      }
    } catch (IllegalArgumentException e) {
      ToolIO.err.println("ERROR: " + e.getMessage() + "\n");
      ToolIO.err.println(HELP_TEXT);
      System.exit(1);
    } catch (XMLExportingException e) {
      ToolIO.err.println(e.toString());
      System.exit(1);
    }
  }

  static class RunOptions {
    public final boolean OfflineMode;
    public final boolean PrettyPrint;
    public final String[] Include;
    public final String TlaFile;
    public RunOptions(boolean offlineMode, boolean prettyPrint, String[] include, String tlaFile) {
      this.OfflineMode = offlineMode;
      this.PrettyPrint = prettyPrint;
      this.Include = include;
      this.TlaFile = tlaFile;
    }
  }

  /**
   * Parses command-line args.
   *
   * @return Null if help request, {@link:RunOptions} instance otherwise.
   * @throws IllegalArgumentException If args are invalid.
   */
  static RunOptions parseArgs(String[] args) {
    List<String> paths = new ArrayList<String>();
    boolean offline_mode = false;
    boolean pretty_print = false;
    String tla_name = null;
    for (int i = 0; i < args.length; i++) {
      if ("-o".equals(args[i])) {
        offline_mode = true;
      } else if ("-p".equals(args[i])) {
        pretty_print = true;
      } else if ("-h".equals(args[i])) {
        return null;
      } else if ("-I".equals(args[i])) {
        i++;
        if (i > args.length - 1) {
          throw new IllegalArgumentException("The -I flag must be followed by a directory path.");
        }
        paths.add(args[i]);
      } else {
        if (null == tla_name) {
          tla_name = args[i];
        } else {
          String message =
            "Unrecognized command-line option " + args[i]
            + "\nNote: only one TLA+ file can be translated per run.";
          throw new IllegalArgumentException(message);
        }
      }
    }

    if (null == tla_name) {
      throw new IllegalArgumentException("At least one .tla file must be given.");
    }

    return new RunOptions(offline_mode, pretty_print, paths.toArray(String[]::new), tla_name);
  }

  /**
   * Parses the given TLA+ spec and outputs the parse tree as XML. The XML is
   * sent to standard output.
   *
   * @param offline_mode If true, skip validating XML against schema.
   * @param pretty_print If true, print human-readable XML.
   * @param paths Paths to use to search for module dependencies.
   * @param tla_name The TLA+ spec to parse.
   * @return Whether parsing & translation was successful.
   * @throws XMLExportingException If serialization to XML failed.
   */
  public static boolean run(
      boolean offline_mode,
      boolean pretty_print,
      String[] paths,
      String tla_name
    ) throws XMLExportingException {

    FilenameToStream fts = new SimpleFilenameToStream(paths);

    // redirecting System.out
    PrintStream out = System.out;
    System.setOut(new PrintStream(new ByteArrayOutputStream()));

    SpecObj spec = new SpecObj(tla_name, fts);

    // Print documentation line on System.out
    ToolIO.out.println("\n****** SANY2 " + SANY.version + "\n");

    // Get next file name from command line; then parse,
    // semantically analyze, and level check the spec started in
    // file Filename leaving the result (normally) in Specification
    // spec.
    // check if file exists
    //ToolIO.out.println("Processing: "+tlas[i]+"\n"+(tlas[i] == null));
    if (FileUtil.createNamedInputStream(tla_name, spec.getResolver()) != null) {
      try {
        SANY.frontEndMain(spec, tla_name, System.err);
        if (spec.getExternalModuleTable() == null)
          throw new XMLExportingException("spec " + spec.getName() + " is malformed - does not have an external module table", null);
        if (spec.getExternalModuleTable().getRootModule() == null)
          throw new XMLExportingException("spec " + spec.getName() + " is malformed - does not have a root module", null);
      } catch (FrontEndException fe) {
        // For debugging
        fe.printStackTrace();
        ToolIO.out.println(fe);
        return false;
      }
    } else {
      ToolIO.out.println("Cannot find the specified file " + tla_name + ".");
      return false;
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
      ModuleNode[] externalModules = table.getModuleNodes();
      for (int j = 0; j < externalModules.length; j++) {
        //Element ext_e = externalModules[j].exportDefinition(doc, context);
        Element ext_e = externalModules[j].export(doc, context);
        rootElement.appendChild(ext_e);
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
      StreamResult result = new StreamResult(out);

      transformer.transform(source, result);
    } catch (ParserConfigurationException pce) {
      throw new XMLExportingException("failed to write XML", pce);
    } catch (TransformerException tfe) {
      throw new XMLExportingException("failed to write XML", tfe);
    } catch (SAXException se) {
      throw new XMLExportingException("failed to validate XML", se);
    }

    return true;
  }

  static void insertRootName(Document doc, Element rootElement, SpecObj spec) {
    Element el = doc.createElement("RootModule");
    el.appendChild(doc.createTextNode(spec.getName()));
    rootElement.insertBefore(el, rootElement.getFirstChild());
  }
}
