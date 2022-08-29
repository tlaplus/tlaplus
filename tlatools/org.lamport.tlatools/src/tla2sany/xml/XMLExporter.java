// Copyright (c) 2013 INRIA-MSR.  All rights reserved.

package tla2sany.xml;

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

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;
import javax.xml.validation.Validator;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.net.URL;
import java.util.LinkedList;

public class XMLExporter {

    static final String JAXP_SCHEMA_LANGUAGE =
            "http://java.sun.com/xml/jaxp/properties/schemaLanguage";
    static final String W3C_XML_SCHEMA =
            "http://www.w3.org/2001/XMLSchema";
    static final String TLA_SCHEMA = "http://tla.msr-inria.inria.fr/tlaps/sany.xsd";
    static final String JAXP_SCHEMA_SOURCE =
            "http://java.sun.com/xml/jaxp/properties/schemaSource";

    public static void main(final String[] args) throws XMLExportingException {

        // parse arguments, possible flag
        // s
        // -I (a modules path) can be repeated
        // -o offline mode (no validation) //TODO: use a resolver to do offline validation
        // then a list of top level modules to parse)
        if (args.length < 1) throw new IllegalArgumentException("at least one .tla file must be given");
        final LinkedList<String> pathsLs = new LinkedList<>();

        boolean offline_mode = false;
        int lastarg = -1; // lastarg will be incremented, initialize at -1
        for (int i = 0; i < args.length - 1; i++) {
            if ("-o".equals(args[i])) {
                offline_mode = true;
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

        final String[] paths = new String[pathsLs.size()];
        for (int i = 0; i < paths.length; i++) paths[i] = pathsLs.get(i);

        if (args.length - lastarg != 1)
            throw new IllegalArgumentException("Only one TLA file to check allowed!");

        final String tla_name = args[lastarg++];

        final FilenameToStream fts = new SimpleFilenameToStream(paths);

        // redirecting System.out
        final PrintStream out = System.out;
        System.setOut(new PrintStream(new ByteArrayOutputStream()));

        final SpecObj spec = new SpecObj(tla_name, fts);

        // Print documentation line on System.out
        ToolIO.out.println("\n****** SANY2 " + SANY.version + "\n");

        // Get next file name from command line; then parse,
        // semantically analyze, and level check the spec started in
        // file Filename leaving the result (normally) in Specification
        // spec.
        // check if file exists
        //ToolIO.out.println("Processing: "+tlas[i]+"\n"+(tlas[i] == null));
        if (FileUtil.namedInputStreamCanBeCreated(tla_name, spec.getResolver())) {
            try {
                var sany = new SANY();
                sany.frontEndMain(spec, tla_name, System.err);
                if (spec.getExternalModuleTable() == null)
                    throw new XMLExportingException("spec " + spec.getName() + " is malformed - does not have an external module table", null);
                if (spec.getExternalModuleTable().getRootModule() == null)
                    throw new XMLExportingException("spec " + spec.getName() + " is malformed - does not have a root module", null);
            } catch (final FrontEndException fe) {
                // For debugging
                fe.printStackTrace();
                ToolIO.out.println(fe);
                return;
            }
        } else {
            ToolIO.out.println("Cannot find the specified file " + tla_name + ".");
            return;
        }


        try {

            final DocumentBuilderFactory docFactory =
                    DocumentBuilderFactory.newInstance();

            // write XML
            final DocumentBuilder docBuilder = docFactory.newDocumentBuilder();

            // root elements
            final Document doc = docBuilder.newDocument();
            final Element rootElement = doc.createElement("modules");
            doc.appendChild(rootElement);
            // Create symbol context. It will be filled by all symbol references during module export.
            final SymbolContext context = new SymbolContext();

            //Export all the external modules
            final ExternalModuleTable table = spec.getExternalModuleTable();
            final ModuleNode[] externalModules = table.getModuleNodes();
            for (final ModuleNode externalModule : externalModules) {
                //Element ext_e = externalModules[j].exportDefinition(doc, context);
                final Element ext_e = externalModule.export(doc, context);
                rootElement.appendChild(ext_e);
            }

            // Insert the symbol table into the beginning of the XML DOM
            rootElement.insertBefore(context.getContextElement(doc), rootElement.getFirstChild());

            //Insert name of root module
            insertRootName(doc, rootElement, spec);

            //Create XML file
            final TransformerFactory transformerFactory = TransformerFactory.newInstance();
            final Transformer transformer = transformerFactory.newTransformer();
            final DOMSource source = new DOMSource(doc);

            // validate the file, do not fail if there is a URL connection error
            if (!offline_mode) { //skip validation in offline mode
                try {
                    final SchemaFactory factory = SchemaFactory.newInstance(W3C_XML_SCHEMA);
                    final Schema schema = factory.newSchema(new URL(TLA_SCHEMA));
                    // create a Validator instance, which can be used to validate an instance document
                    final Validator validator = schema.newValidator();
                    //validate the DOM tree
                    validator.validate(source);
                } catch (final java.io.IOException ioe) {
                    // do nothing if there is no internet connection
                    // but fail for other errors
                }
          /*catch (org.xml.sax.SAXParseException spe) {
            // do nothing if there is no internet connection
            // but fail for other errors
          }*/
            }
            final StreamResult result = new StreamResult(out);

            transformer.transform(source, result);
        } catch (final ParserConfigurationException | TransformerException pce) {
            throw new XMLExportingException("failed to write XML", pce);
        } catch (final SAXException se) {
            throw new XMLExportingException("failed to validate XML", se);
        }

    }

    static void insertRootName(final Document doc, final Element rootElement, final SpecObj spec) {
        final Element el = doc.createElement("RootModule");
        el.appendChild(doc.createTextNode(spec.getName()));
        rootElement.insertBefore(el, rootElement.getFirstChild());
    }
}
