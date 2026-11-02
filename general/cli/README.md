# TLA+ CLI Wrappers

This directory contains a lightweight command-line wrapper for the TLA+ tools
provided in `tla2tools.jar`.

## Overview

The TLA+ tools are typically invoked via Java class names, for example:

```bash
  java -cp tla2tools.jar tlc2.TLC
```

This wrapper provides a more convenient interface:

```bash
tla <command> [args]
```

Available commands:
- `tlc` Run the model checker
- `sany` Parse a TLA+ specification
- `repl` Start the TLA+ REPL
- `pcal` Translate PlusCal to TLA+
- `tla2tex` Export TLA+ to LaTeX

Examples:
```bash
tla tlc Spec.tla
tla sany Spec.tla
```

## Requirements

- Java 11+
- `tla2tools.jar`, available from the official releases of the
  TLA+ project

## Setup

Download `tla2tools.jar` from the official releases and set the environment variable:

```sh
export TLA_JAR=/path/to/tla2tools.jar
