Overview
--------
[![](https://github.com/tlaplus/tlaplus/workflows/CI/badge.svg?branch=master)](https://github.com/tlaplus/tlaplus/actions?query=workflow%3ACI)
[![Sonatype Nexus (Snapshots)](https://img.shields.io/nexus/s/org.lamport/tla2tools?server=https%3A%2F%2Foss.sonatype.org)](https://oss.sonatype.org/content/repositories/snapshots/org/lamport/tla2tools/)

This repository hosts the core TLA⁺ command line interface (CLI) Tools and the Toolbox integrated development environment (IDE).
Its development is managed by the [TLA⁺ Foundation](https://foundation.tlapl.us/).
See http://tlapl.us for more information about TLA⁺ itself.
For the TLA⁺ proof manager, see http://proofs.tlapl.us.

Versioned releases can be found on the [Releases](https://github.com/tlaplus/tlaplus/releases) page.
Currently, every commit to the master branch is built & uploaded to the [1.8.0 Clarke pre-release](https://github.com/tlaplus/tlaplus/releases/tag/v1.8.0).
If you want the latest fixes & features you can use that pre-release.
If you want to consume the TLA⁺ tools as a Java dependency in your software project, Maven packages are periodically published to [oss.sonatype.org](https://oss.sonatype.org/content/repositories/snapshots/org/lamport/tla2tools/).

Use
---
The TLA⁺ tools require Java 11+ to run.
The `tla2tools.jar` file contains multiple TLA⁺ tools.
They can be used as follows:
```bash
java -cp tla2tools.jar tla2sany.SANY -help  # The TLA⁺ parser
java -cp tla2tools.jar tlc2.TLC -help       # The TLA⁺ finite model checker
java -cp tla2tools.jar tlc2.REPL            # Enter the TLA⁺ REPL
java -cp tla2tools.jar pcal.trans -help     # The PlusCal-to-TLA⁺ translator
java -cp tla2tools.jar tla2tex.TLA -help    # The TLA⁺-to-LaTeX translator
```
If you add `tla2tools.jar` to your [`CLASSPATH`](https://docs.oracle.com/javase/tutorial/essential/environment/paths.html) environment variable then you can skip the `-cp tla2tools.jar` parameter.
Running `java -jar tla2tools.jar` is aliased to `java -cp tla2tools.jar tlc2.TLC`.

Developing & Contributing
-------------------------
The TLA⁺ Tools and Toolbox IDE are both written in Java.
The TLA⁺ Tools source code is in [tlatools/org.lamport.tlatools](./tlatools/org.lamport.tlatools).
The Toolbox IDE is based on [Eclipse Platform](https://github.com/eclipse-platform) and is in the [toolbox](./toolbox) directory.
For instructions on building & testing these as well as setting up a development environment, see [DEVELOPING.md](DEVELOPING.md).

We welcome your contributions to this open source project!
TLA⁺ is used in safety-critical systems, so we have a contribution process in place to ensure quality is maintained; read [CONTRIBUTING.md](CONTRIBUTING.md) before beginning work.

Copyright History
-----------------
Copyright (c) 199?-2003 HP Corporation  
Copyright (c) 2003-2020 Microsoft Corporation

Licensed under the [MIT License](http://lamport.azurewebsites.net/tla/license.html)
