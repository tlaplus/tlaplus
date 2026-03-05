Overview
--------
[![](https://github.com/tlaplus/tlaplus/workflows/CI/badge.svg)](https://github.com/tlaplus/tlaplus/actions?query=workflow%3ACI)
[![Maven Snapshot](https://img.shields.io/badge/maven-1.8.0--SNAPSHOT-blue)](https://central.sonatype.com/repository/maven-snapshots/org/lamport/tla2tools/)

This repository hosts the core TLA⁺ command line interface (CLI) Tools and the Toolbox integrated development environment (IDE).
Its development is managed by the [TLA⁺ Foundation](https://foundation.tlapl.us/).
See http://tlapl.us for more information about TLA⁺ itself.
For the TLA⁺ proof manager, see http://proofs.tlapl.us.

Versioned releases can be found on the [Releases](https://github.com/tlaplus/tlaplus/releases) page.
Currently, every commit to the master branch is built & uploaded to the [1.8.0 Clarke pre-release](https://github.com/tlaplus/tlaplus/releases/tag/v1.8.0).
If you want the latest fixes & features you can use that pre-release.
If you want to consume the TLA⁺ tools as a Java dependency in your software project, Maven packages are periodically published to [central.sonatype.org](https://central.sonatype.com/repository/maven-snapshots/org/lamport/tla2tools/1.8.0-SNAPSHOT/).

Use
---
The TLA⁺ tools require Java 11+ to run.

To use TLA⁺ from a graphical interface, see [the TLA⁺ VS Code extension](https://github.com/tlaplus/vscode-tlaplus/).
The Eclipse-based TLA⁺ Toolbox GUI is also available from this repository, but it is currently unmaintained.

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

For more information on using & consuming the TLA⁺ tools, see [`USE.md`](./USE.md).

Developing & Contributing
-------------------------
The TLA⁺ Tools and Toolbox IDE are both written in Java.
The TLA⁺ Tools source code is in [tlatools/org.lamport.tlatools](./tlatools/org.lamport.tlatools).
The Toolbox IDE is based on [Eclipse Platform](https://github.com/eclipse-platform) and is in the [toolbox](./toolbox) directory.
For instructions on building & testing these as well as setting up a development environment, see [DEVELOPING.md](DEVELOPING.md).

We welcome your contributions to this open source project!
TLA⁺ is used in safety-critical systems, so we have a contribution process in place to ensure quality is maintained; read [CONTRIBUTING.md](CONTRIBUTING.md) before beginning work.

License & Copyright
-----------------
Copyright © 199? HP Corporation
Copyright © 2003 Microsoft Corporation
Copyright © 2023 Linux Foundation

Licensed under the [MIT License](LICENSE).

