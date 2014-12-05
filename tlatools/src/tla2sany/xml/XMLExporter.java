
// Copyright (c) 2013 INRIA-MSR.  All rights reserved.

package tla2sany.xml;

/**
 * a tool for exporting the loaded modules to XML format
 */

import java.io.PrintStream;
import java.io.ByteArrayOutputStream;
import java.util.Iterator;
import java.util.LinkedList;

import tla2sany.drivers.SANY;
import tla2sany.drivers.FrontEndException;
import tla2sany.configuration.Configuration;
import tla2sany.explorer.Explorer;
import tla2sany.explorer.ExplorerQuitException;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.ParseException;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.BuiltInLevel;
import tla2sany.semantic.Context;
import tla2sany.semantic.Errors;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.Generator;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.st.Location;
import tla2sany.semantic.ModuleNode;
import util.FileUtil;
import util.ToolIO;
import util.UniqueString;
import util.FilenameToStream;
import util.SimpleFilenameToStream;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.TheoremNode;
import tla2sany.semantic.InstanceNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;


// XML packages
import java.io.File;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.validation.SchemaFactory;
import javax.xml.validation.Schema;
import javax.xml.validation.Validator;
import org.xml.sax.SAXException;
import java.net.URL;
import java.net.MalformedURLException;

import org.w3c.dom.Attr;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class XMLExporter {

  static final String JAXP_SCHEMA_LANGUAGE =
        "http://java.sun.com/xml/jaxp/properties/schemaLanguage";
  static final String W3C_XML_SCHEMA =
        "http://www.w3.org/2001/XMLSchema";
  static final String TLA_SCHEMA = "http://tla.msr-inria.inria.fr/tlaps/sany.xsd";
  static final String JAXP_SCHEMA_SOURCE =
        "http://java.sun.com/xml/jaxp/properties/schemaSource";

  public static final void main(String[] args) throws XMLExportingException {

    // parse arguments, possible flag
    // s
    // -I (a modules path) can be repeated
    // then a list of top level modules to parse)
    if (args.length < 1) throw new IllegalArgumentException("at least one .tla file must be given");

    LinkedList pathsLs = new LinkedList();
    int ind = 0;
    while (args[ind].equals("-I")) {
      ind++;
      if (ind > args.length-2) throw new IllegalArgumentException("the -I flag must be followed by a directory and at least one .tla file");
      pathsLs.addLast(args[ind++]);
      if (ind > args.length-1) throw new IllegalArgumentException("at least one .tla file must be given");
    }

    String[] paths = new String[pathsLs.size()];
    for (int i=0; i<paths.length; i++) paths[i] = (String)pathsLs.get(i);

    String[] tlas = new String[args.length - ind];
    for (int i=0; i<args.length-ind; i++) tlas[i] = args[ind++];

    FilenameToStream fts = new SimpleFilenameToStream(paths);

    // redirecting System.out
    PrintStream out = System.out;
    System.setOut(new PrintStream(new ByteArrayOutputStream()));

    SpecObj[] specs = new SpecObj[tlas.length];
    for (int i=0; i<tlas.length; i++) specs[i] = new SpecObj(tlas[i], fts);

    // For each file named on the command line (i.e. in the tlas
    // array) (re)initialize the entire system and process that file
    // as the root of a new specification.
    for (int i = 0; i < tlas.length; i++) {
      // continue the loop where the last one left off
      // Print documentation line on System.out
      ToolIO.out.println("\n****** SANY2 " + SANY.version + "\n") ;

      // Get next file name from command line; then parse,
      // semantically analyze, and level check the spec started in
      // file Filename leaving the result (normally) in Specification
      // spec.
      // check if file exists
      if (FileUtil.createNamedInputStream(tlas[i], specs[i].getResolver()) != null)
      {
          try {
              SANY.frontEndMain(specs[i], tlas[i], System.err);
              if (specs[i].getExternalModuleTable() == null)
                throw new XMLExportingException("spec " + specs[i].getName() + " is malformed - does not have an external module table", null);
              if (specs[i].getExternalModuleTable().getRootModule() == null)
                throw new XMLExportingException("spec " + specs[i].getName() + " is malformed - does not have a root module", null);
            }
            catch (FrontEndException fe) {
              // For debugging
              fe.printStackTrace();
              ToolIO.out.println(fe);
              return;
            }
      } else
      {
          ToolIO.out.println("Cannot find the specified file " + tlas[i] + ".");
      }
    }

    try {

      DocumentBuilderFactory docFactory =
            DocumentBuilderFactory.newInstance();
      /* validation is being done later
      docFactory.setNamespaceAware(true);
      docFactory.setValidating(true);
      docFactory.setAttribute(JAXP_SCHEMA_LANGUAGE, W3C_XML_SCHEMA);
      docFactory.setAttribute(JAXP_SCHEMA_SOURCE, TLA_SCHEMA);
      */

      // write XML
      DocumentBuilder docBuilder = docFactory.newDocumentBuilder();

      // root elements
      Document doc = docBuilder.newDocument();
      Element rootElement = doc.createElement("modules");
      doc.appendChild(rootElement);
      SymbolContext context = new SymbolContext();
      for (int i=0; i<specs.length; i++) {
        Element e = specs[i].getExternalModuleTable().getRootModule().exportDefinition(doc,context);
        rootElement.appendChild(e);
      }
      // at the beginning, we append the context of the symbols used in this node
      rootElement.insertBefore(context.getContextElement(doc), rootElement.getFirstChild());

      TransformerFactory transformerFactory = TransformerFactory.newInstance();
      Transformer transformer = transformerFactory.newTransformer();
      DOMSource source = new DOMSource(doc);

      // validate the file, do not fail if there is a URL connection error
      try {
        SchemaFactory factory = SchemaFactory.newInstance(W3C_XML_SCHEMA);
        Schema schema = factory.newSchema(new URL(TLA_SCHEMA));
        // create a Validator instance, which can be used to validate an instance document
        Validator validator = schema.newValidator();
        //validate the DOM tree
        validator.validate(source);
      }
      catch (java.io.IOException ioe) {
        // do nothing if there is no internet connection
        // but fail for other errors
      }
      /*catch (org.xml.sax.SAXParseException spe) {
        // do nothing if there is no internet connection
        // but fail for other errors
      }*/

      StreamResult result = new StreamResult(out);

      transformer.transform(source, result);
    }
    catch (ParserConfigurationException pce) {
      throw new XMLExportingException("failed to write XML", pce);
    } catch (TransformerException tfe) {
      throw new XMLExportingException("failed to write XML", tfe);
    } catch (SAXException se) {
      throw new XMLExportingException("failed to validate XML", se);
    }
  }
}
