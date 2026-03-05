# Using the TLA⁺ Tools

This document covers several modes of use for the TLA⁺ tools, outside of the common GUI-based [TLA⁺ VS Code extensions](github.com/tlaplus/vscode-tlaplus/).
The tools require Java 11+ to run.

## From the Command Line

Get `tla2tools.jar` from the [releases](https://github.com/tlaplus/tlaplus/releases) to use the tools from the command line.
The `tla2tools.jar` file contains multiple TLA⁺ tools; after adding `tla2tools.jar` to your [`CLASSPATH`](https://docs.oracle.com/javase/tutorial/essential/environment/paths.html), the tools can be used as follows:
```bash
EXPORT CLASSPATH=tla2tools.jar
java tla2sany.SANY -help  # The TLA⁺ parser
java tlc2.TLC -help       # The TLA⁺ model checker
java tlc2.REPL            # Enter the TLA⁺ REPL
java pcal.trans -help     # The PlusCal-to-TLA⁺ translator
java tla2tex.TLA -help    # The TLA⁺-to-LaTeX translator
java tla2sany.xml.XMLExporter -help # Export TLA⁺ parse tree as XML
```
Running `java -jar tla2tools.jar` is aliased to run `tlc2.TLC`.


## From a Java Application

To use the TLA⁺ tools as a library from a Java application, you can specify the [Maven package](https://central.sonatype.com/repository/maven-snapshots/org/lamport/tla2tools/1.8.0-SNAPSHOT/) as a dependency of your project.

### Parsing with SANY

To parse a TLA⁺ spec with SANY from your Java application, call the `tla2sany.drivers.SANY.parse()` function.
This function is process-safe but not thread-safe, meaning it can be called concurrently from independent processes but not concurrently from separate threads within the same process.
The function accepts a `tla2sany.modanalyzer.SpecObj` object as a parameter which will be populated with the parsed spec information.
If parsing is successful, the method returns `tla2sany.drivers.SanyExitCode.OK`.

### Model-Checking with TLC

To model-check a TLA⁺ specification with TLC, call `tlc2.TLC.main()` with a list of arguments, the same as on the command line.
Note that TLC cannot be run twice in a row from within the same process as it maintains global static state which must be re-initialized by reloading its classes.

## From a non-Java Application

The TLA⁺ tools implement several export formats to facilitate development with non-Java applications.
These all require running Java on `tla2tools.jar` using whatever command line invocation utilities your language possesses, then capturing the process's output.

### Parsing with SANY

To parse a TLA⁺ spec from a non-Java application, run the XML Exporter (`tla2sany.xml.XMLExporter`) from your program and capture its standard output.
This output is an XML representation of SANY's abstract syntax tree (AST).
Your application can consume and process this AST to create any desired TLA⁺ language tooling.
The primary documentation of the XML format is found in [this XML Schema Definition file](./tlatools/org.lamport.tlatools/src/tla2sany/xml/sany.xsd).

### Model-Checking with TLC

To use the TLC model checker (`tlc2.TLC`) from a non-Java application, the full state space can be dumped to a file in the [DOT graph description language](https://en.wikipedia.org/wiki/DOT_(graph_description_language)) format with the `-dump dot output.gv` option.
Model error traces can also be dumped to & loaded from JSON using `-dumpTrace json output.json` and `-loadTrace json input.json` to support model-based testing and trace validation.

