# Using the TLA⁺ Tools

To use the TLA⁺ tools as a library from a Java application, you can specify the [Maven package](https://central.sonatype.com/repository/maven-snapshots/org/lamport/tla2tools/1.8.0-SNAPSHOT/) as a dependency of your project.
Note that if you want to run the tools concurrently, they are generally process-safe but not thread-safe.
TLC (the model-checker) in particular cannot be run twice in a row from within the same process as it maintains global static state which must be re-initialized by reloading its classes.
SANY (the parser) is safe to run multiple times sequentially from within the same process.

To use the TLA⁺ parser (SANY) from a non-Java application, the XML Exporter (`tla2sany.xml.XMLExporter`) fully parses a TLA⁺ specification and outputs its abstract syntax tree as XML.
Your application can consume and process this XML AST to create any desired TLA⁺ language tooling.
The primary documentation of the XML format is found in [this XML Schema Definition file](./tlatools/org.lamport.tlatools/src/tla2sany/xml/sany.xsd).

To use the TLC model checker (`tlc2.TLC`) from a non-Java application, the full state space can be dumped to a file in the [DOT graph description language](https://en.wikipedia.org/wiki/DOT_(graph_description_language)) format with the `-dump dot output.gv` option.
Model error traces can also be dumped to & loaded from JSON using `-dumpTrace json output.json` and `-loadTrace json input.json` to support model-based testing and trace validation.

