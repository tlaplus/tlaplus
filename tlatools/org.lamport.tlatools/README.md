# TLA Tools
## Introduction
This project builds the tlatools.jar that contains. This can be used standalone on the command line, or through the Toolbox or the VSCode plugin.

It contains the following functionality:

- PCal Processor
- TLA+ Language Parsing
- TLC Model Checker / Simulator / Debugger
- TLA+ to TeX conversion

Information on how to use these tools can be found [here](http://lamport.azurewebsites.net/tla/tools.html).

The content below is a "Getting Started" guide to developing on this codebase. It covers the majority of building, testing and packaging operations. New developers should also read the [codebase overview](docs/CodebaseOverview.md) to help orient themselves.

## Development Prerequisites
- [Maven](https://maven.apache.org/)

## Supported IDEs
This project has configuration for the following IDEs:
- Eclipse
- IntelliJ
- VSCode

Note that the majority of the configuration is derived from the Maven project, so you may need to reimport the maven project if it has changed. For certain changes this may involve sometimes requires deleting the project file.

There are certain features of this project that are built specifically for the Eclipse IDE.

## Compiling
### From IDE
Standard IDE compilation will work without additional steps.

### From Maven

``` shell
mvn compile
```

## Standard Testing
### From IDE
This project has specific testing requirements that need to be set up for testing to work from test runners. This is done through the following command:

``` shell
mvn test-compile
```

Then you can run any specific test with the test runner. You can also use standard test debugging features.

### With Maven
For standard testing, run:

``` shell
mvn test
```

If you want incremental builds for testing, use the command below. It only cleans output directories, and so can shorten build time dramatically.

``` shell
mvn test -P dev
```

## Packaging
To follow the standard release workflow run:

``` shell
mvn verify -P test-dist
```

> Note: A profile is necessary because testing the distribution excludes compile dependencies from the classpath, and can effect IDES

If you do not want to run integration tests against the created jar file, run:
``` shell
mvn package
```

If you want to skip running the standard tests, so they will be run against the jar, run:
``` shell
mvn verify -P test-dist -Dskip.surefire.tests=true
```

## Benchmarking

To build and run all the benchmarks, run:
``` shell
mvn verify -P benchmark
```

To run a specific benchmark
``` shell
mvn verify -P benchmark -Dbenchmark.class=BENCHMARK_CLASS_WITH_PACKAGE
```

To just build the jmh benchmark jar, run:
``` shell
mvn package -P benchmark
```

[See additional instructions](test-benchmark/README.md) on running the benchmark from eclipse .

## Java Pathfinder Verification
For details on pathfinder verification, see the [readme](test-verify/README.md).


## Long Tests

Long tests can only be easily run from maven:

``` shell
mvn verify -P aspectj,test-long
```

Due to the aspectj dependency, additional configuration would be needed to run them from the IDE.

To skip the multi-hour tests, run the following command:

``` shell
mvn verify -P aspectj,test-long -Dskip.tests.very-long=true
```

## Tips

One tip, if you want to record the output of some tlatool (like if you
were seeing the CLI stdout/stderr), you can use [TestPrintStream](test/util/TestPrintStream.java) in
combination with [ToolIO](src/util/ToolIO.java). Search for them in the codebase.