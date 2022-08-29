# Codebase Overview

The tlatools codebase is a complex one, there are over 600k lines of code, in over 2000 files, written over 20+ years. And yet as the best distributed systems modelling tool on the market today, maintaining and improving it is critical.

This overview is meant to orient new programmers as well as reorient existing ones. 

## Table of Contents 
- [Codebase Overview](#codebase-overview)
  - [Table of Contents](#table-of-contents)
  - [Java Version](#java-version)
  - [Quality Standards](#quality-standards)
    - [Treat Warnings as Errors](#treat-warnings-as-errors)
    - [No Unnecessary Mutable Static State](#no-unnecessary-mutable-static-state)
    - [Minimal Memory Leaks](#minimal-memory-leaks)
    - [Ensure Test Coverage](#ensure-test-coverage)
  - [Codebase Architecture Walkthrough](#codebase-architecture-walkthrough)
    - [Modules](#modules)
    - [The Standard Flow](#the-standard-flow)
    - [Model Checker Analysis](#model-checker-analysis)
    - [Depth-First Checker Analysis](#depth-first-checker-analysis)
    - [Simulator Analysis](#simulator-analysis)
    - [Liveness Checking](#liveness-checking)
    - [States and Fingerprints](#states-and-fingerprints)
    - [High Performance Datastructures](#high-performance-datastructures)
      - [Fingerprint Sets (FPSets)](#fingerprint-sets-fpsets)
      - [StateQueue](#statequeue)
    - [Symmetry Sets](#symmetry-sets)
    - [Debugger](#debugger)
    - [Coverage](#coverage)
    - [Unique Strings](#unique-strings)
  - [Deprecated Dependencies](#deprecated-dependencies)
    - [`sun.misc.Unsafe`](#sunmiscunsafe)
    - [`java.lang.String.getBytes(int srcBegin, int srcEnd, byte[] dst, int dstBegin)`](#javalangstringgetbytesint-srcbegin-int-srcend-byte-dst-int-dstbegin)
  - [Codebase Idiosyncrasies](#codebase-idiosyncrasies)
    - [Dynamic Class Loading](#dynamic-class-loading)
      - [Operators / Modules](#operators--modules)
      - [FPSet Selection](#fpset-selection)
      - [Misc](#misc)
    - [Notable Mutable Static State](#notable-mutable-static-state)
    - [Testing Brittleness](#testing-brittleness)
      - [Independently Run Tests](#independently-run-tests)
      - [Unique String ordering reliance](#unique-string-ordering-reliance)
      - [Debugger Tests](#debugger-tests)
    - [Primitive Versions of Standard Data Structures](#primitive-versions-of-standard-data-structures)
    - [Unchecked Casting](#unchecked-casting)
    - [Dead Code](#dead-code)
      - [Acceptable Dead Code](#acceptable-dead-code)
      - [Dead Code to be Removed](#dead-code-to-be-removed)
    - [Inconsistent Formatting](#inconsistent-formatting)
    - [JMX / Eclipse Integrations](#jmx--eclipse-integrations)
    - [Java Pathfinder](#java-pathfinder)

## Java Version
The project is currently targeting Java 17 LTS. This is meant to somewhat future-proof the project, with support [available until 2029](https://www.oracle.com/java/technologies/java-se-support-roadmap.html). It is likely it will be compatible with new java runtimes. This project currently compiles for JDK 18, and hopefully will work with newer versions of java for users who require it.

> Note: There are a number of performance improvements to be rolled out in the upcoming JDKs that certain users may wish to take advantage of.

## Quality Standards
Because of the complexity of the codebase, adhering to these quality standards is critical.

### Treat Warnings as Errors
The codebase currently outputs no warnings (except for the unavoidable and unsuppressible sun.misc.unsafe one). This should be maintained.
Occasionally, introducing a warning may be required. Every warning remaining in the project has been inspected, and suppressed if appropriate. This should be rare for new code, and be done sparingly.

### No Unnecessary Mutable Static State
Refrain, if possible, from introducing global state. While legacy code does use some static state, it is challenging to debug and can cause problems for test runs. 

### Minimal Memory Leaks
The codebase currently has very few memory leaks. This improves testability, and also improves debugging by making heap dumps representative.
After an operation is run, whenever possible the memory should be cleared. This can be tested by pausing execution at the test "tearDown" function and inspecting the heap dump. 

Use the AutoCloseable interface and semantics where appropriate.

> Note: Don't forget to account for JMX beans! They must be explicitly unregistered in the close function.

### Ensure Test Coverage
The large end to end test suite is one of the project's greatest assets. Ensure that any new functionality is tested, preferably end to end.

As the codebase is somewhat brittle, ensuring your feature is tested is the only way to help others not break your code.

<br>

## Codebase Architecture Walkthrough
### Modules
- [pcal](../src/pcal): Converts the pcal language into TLA+ that can by run by TLC2.
- [tla2tex](../src/tla2tex): "Pretty Prints" TLA+ code into LaTex. This LaTex can then be used for publishing.
- [tla2sany](../src/tla2sany): Contains the AST and parsing logic for the TLA+ language. The AST classes generated from parsing are used by TLC2.
- [tlc2](../src/tlc2): The model checker to validate the AST generated by tla2sany. This is the largest and most complex part of the codebase by far.

### The Standard Flow
This is a generalized mplified description of how this code is normally used, and the involved components. More detail will be given on some of these components in the following sections.

1. (Optional) PCal code translated into TLA+ code. [pcal.trans](src/pcal/trans.java)::main
2. TLC2 Model Checker run from standard entrypoint [tlc2.TLC](src/tlc2/TLC.java)::main on that code and associated .cfg file
3. TLC2 class created, arguments parsed, and processing started. [tlc2.TLC](src/tlc2/TLC.java)::TLC, TLC::handleParameters, TLC::process
4. The spec is parsed and stored in [Tool](../src/tlc2/tool/impl/Tool.java). This occurs in the Tool constructor.
   1. A [SpecObj](../src/tla2sany/modanalyzer/SpecObj.java) is created with file information about the spec
   2. A [SpecProcessor](../src/tlc2/tool/impl/SpecProcessor.java) is created with that SpecObj
   3. At the start of processing the spec, SpecProcessor calls [SANY](../src/tla2sany/drivers/SANY.java)::frontEndMain that parses the spec into an AST
   4. The SpecProcessor performs a number of extraction and analysis operations on the AST.
        > Note: These are called in a precise order in the [Tool](../src/tlc2/tool/impl/Tool.java) constructor. Modifying this is highly error prone, though the tests will fail reliably if there is an issue.
   5. The Tool takes the results of all these operations and assigns them to final variables. The Tool is now the only source of truth for specification information, and is immutable.
        > Note: This is a critical separation of concerns, to separate the complex job of parsing and resolving the spec, from the job of analyzing it. The tool is the only object that spans both.
5. The following are selected and initialized
    - The model checker or simulator. This class performs a certain type of analysis on the spec.
      - [ModelChecker](../src/tlc2/tool/ModelChecker.java): Standard Breadth-First checking of entire state space
        - [FPSet](../src/tlc2/tool/fp/FPSet.java): Contains the fingerprints of all explored states.
        - [StateQueue](../src/tlc2/tool/queue/IStateQueue.java): Contains new states to explore.
      - [DFIDModelChecker](../src/tlc2/tool/DFIDModelChecker.java): Depth first checking of entire state space, to a pre-specified level of depth.
        - [FPIntSet](../src/tlc2/tool/fp/dfid/FPIntSet.java)
      - [Simulator](../src/tlc2/tool/Simulator.java): Randomized exploration and checking of the state space.
6. The analysis is performed
    1. Workers are run per configuration to allow multi-threaded analysis
        - ModelChecker: [Worker](../src/tlc2/tool/Worker.java)
        - DFIDModelChecker: [DFIDWorker](../src/tlc2/tool/DFIDWorker.java)
        - Simulator: [SimulationWorker](../src/tlc2/tool/SimulationWorker.java)
    2. Each checker performs analysis differently, but generally the analysis consists of generating new states from existing states, and checking those new states
7. The result is returned to the user

### Model Checker Analysis

1. The StateQueue is seeded with the initial states
2. Workers take states of the StateQueue. From there they generate next potential states. They check that the fingerprint of the state is not already in the FPSet (such that analysis is not duplicated). They then check that state for safety properties, and add it to both the FPSet and the StateQueue.'
3. Periodically the analysis pauses. If configured to create a checkpoint, a checkpoint is created. If configured to check temporal properties, the Liveness Checking workflow (described below) is performed by calling [LiveChecker](../src/tlc2/tool/liveness/LiveCheck.java)::check. Once done the analysis continues.
4. When the StateQueue is empty or an error is detected, the analysis is over. 

> Performance Note: The vast majority of CPU cycles are spent either calculating fingerprints or storing fingerprints in the FPSet.                        

### Depth-First Checker Analysis

1. Data structure initialized with InitStates
2. The analysis occurs by setting a temporary max depth that increases to the configured maximum depth
3. Worker retrieves unexplored initial state, removing it from the set of init states
4. Worker explores the state space depth first up to the temporary max depth, storing all seen states in the FPIntSet
5. Periodically the analysis pauses. If configured to create a checkpoint, a checkpoint is created. If configured to check temporal properties, the Liveness Checking workflow (described below) is performed by calling [LiveCheck](../src/tlc2/tool/liveness/LiveCheck.java)::check. Once done the analysis continues.
6. Once there are no more levels to explore, or an error is detected, the analysis is over


### Simulator Analysis

1. Initial states calculated and checked for validity
2. Each SimulationWorker retrieves a random initial state
3. Next states are randomly generated and checked, up to a specified depth. Each one of these runs is a trace.
4. If liveness checking is enabled, check the trace with [LiveChecker](../src/tlc2/tool/liveness/LiveCheck.java)::checkTrace
5. Once the specified number of traces have been run, or an error is detected, the analysis is over

### Liveness Checking
Liveness checking is what allows checking of temporal properties.

Liveness checking is initiated by calling: [LiveCheck](../src/tlc2/tool/liveness/LiveCheck.java)::check or checkTrace.

Every time this occurs it creates new [LiveWorker](../src/tlc2/tool/liveness/LiveWorker.java)(s) to perform the analysis.

> Note: Unlike standard model checking, Liveness Checking by default is not guaranteed to produce the shortest trace that violates the properties. There is a [AddAndCheckLiveCheck](../src/tlc2/tool/liveness/AddAndCheckLiveCheck.java) that extends LiveCheck that attempts to do this, at the cost of significant performance. It is selected in the constructor of [AbstractChecker](../src/tlc2/tool/AbstractChecker.java).

### States and Fingerprints
States are a fundamental part of TLC. They represent a set of variable values, that entirely determine the state of the system. States are generated and checked as part of the TLC2 analysis process. The base class for this is [TLCState](../src/tlc2/tool/TLCState.java).

Fingerprints are hashes taken of these states using the [FP64](src/tlc2/util/FP64.java) hash. Fingerprints are a 64bit hash representing the state. This is significantly smaller than storing the state itself, and yet collisions are very unlikely (though if they did occur, part of the statespace would not be explored). The fingerprinting process is initiated from [TLCState](../src/tlc2/tool/TLCState.java)::generateFingerPrint. 

There are two primary implementations of state that are very similar:
- [TLCStateMut](../src/tlc2/tool/TLCStateMut.java): Higher performance, records less information
- [TLCStateMutExt](../src/tlc2/tool/TLCStateMutExt.java): Lower performance, records more information

Effectively, functions that are no-ops in TLCStateMut, persistently store that information in TLCStateMutExt. This information can include the name of the generating action, and is often needed for testing / debugging purposes.

The implementation to use is selected in the constructor of [Tool](../src/tlc2/tool/impl/Tool.java), by setting a reference Empty state for the analysis.

### High Performance Datastructures

The ModelChecker performs a breadth-first search. In a standard BFS algorithm, there are two main datastructures: a queue of items of explore next, and a set of the nodes already explored. Because of the sheer size of the state space for the ModelChecker, specialized versions of these datastructures are used.

> Note: These data-structures are a large focus of the profiling / testing work, because both performance and correctness are key for the ModelChecker to explore the full state space.

#### Fingerprint Sets (FPSets)
FPSets are sets with two main operations
- put fingerprint
- determine if fingerprint in set

Located in [tlc2.tool.fp](../src/tlc2/tool/fp). All but [FPIntSet](../src/tlc2/tool/fp/dfid/FPIntSet.java) extend [FPSet](../src/tlc2/tool/fp/FPSet.java). FPIntSet is used specifically for depth-first-search and is not discussed here.

In practice the performance and size of the FPSet determine the extent of analysis possible. The [OffHeapDiskFPSet](../src/tlc2/tool/fp/OffHeapDiskFPSet.java) is in practice the most powerful of the FPSets, efficiently spanning the operations across off-heap memory and the disk. There are also memory only FPSets that may be preferable for smaller state spaces.

#### StateQueue
Located in [tlc2.tool.queue](../src/tlc2/tool/queue), with all implementations extending [StateQueue](../src/tlc2/tool/queue/StateQueue.java).

The default implementation is [DiskStateQueue](../src/tlc2/tool/queue/DiskStateQueue.java). Because of the size of the queue, storing it in memory may not be an option.

### Symmetry Sets
A discussion of Symmetry Sets can be found [here](https://www.learntla.com/core/constants.html).

They are implemented in the [TLCState](../src/tlc2/tool/TLCState.java)::generateFingerPrint function by calculated all permutations of a particular state (for all symmetry set model values), and returning the smallest fingerprint. Therefore all permutations would have a same fingerprint, and so only the first example generated would be explored.

> Note: The order dependant nature of the fingerprint means that when using symmetry sets, the majority of the cpu cycles are spent "normalizing" the data structures such that the order the fingerprint gets assembled in are consistent. An order independent fingerprint hash would remove this performance hit, however would significantly increase the likelihood of collisions unless the hash algorithm itself was upgraded.

### Debugger
The [AttachingDebugger](../src/tlc2/debug/AttachingDebugger.java) is the main debugger. It works in conjunction with the [DebugTool](../src/tlc2/tool/impl/DebugTool.java) to allow a user to step through a TLC execution.

> Note: Using the debugger will keep the process alive indefinitely due to the listener. The eclipse network listener is not interruptable, so thread interruption behavior will not work. It relies on process exit.

### Coverage
The coverage functionality determines what statements in the TLA+ spec have been used.
Located in [tlc2.tool.coverage](../src/tlc2/tool/coverage)

### Unique Strings
String comparison can be a relatively expensive operation compared to primitive comparison. There are lots of string comparisons required in the code, but with a relatively limited set of strings.[UniqueString](../src/util/UniqueString.java) maps each string to a monotonically increasing integer. Then comparisons are reduced to the much cheaper integer comparisons. This is used throughout the codebase.

## Deprecated Dependencies
These deprecated methods/dependencies should be removed whenever technically feasible. Currently use of deprecated features is very limited (and called out in this document). Introducing new functionality depending on deprecated features is not recommended.

> Warnings for these have been suppressed where possible, as they are known and accounted for.

### `sun.misc.Unsafe`
Used by: [LongArray](../src/tlc2/tool/fp/LongArray.java)

While this could be replaced with `jdk.internal.misc.Unsafe`, it would require a commandline flag to work "--add-opens=java.base/jdk.internal.misc=ALL-UNNAMED", or could potentially be added to the mainfest with a "Add-Opens:" tag (though this functionality is poorly documented).

Fundamentally removing unsafe code is not feasible, because as of JDK 18, java does not have a high performance off-heap memory segment with compare and swap functionality (to allow lock-free programming). [MemorySegment](https://docs.oracle.com/en/java/javase/18/docs/api/jdk.incubator.foreign/jdk/incubator/foreign/MemorySegment.html) which is still in incubation is the closest, but still not workable. It is unlikely java will deprecate the unsafe API until they can replace this functionality.

### `java.lang.String.getBytes(int srcBegin, int srcEnd, byte[] dst, int dstBegin)`
Used by: [BufferedDataOutputStream](../src/util/BufferedDataOutputStream.java)

The difficulty is that the new methods require getting all the bytes in the string, rather than selecting them in the function. However, likely this efficiency is not needed if this method every becomes terminally deprecated.

## Codebase Idiosyncrasies

As a 20 year old code base, one can expect idiosyncrasies that do not match current best practice. There are also inherent idiosyncrasies to any language interpreter. Maintaining functionality and performance is the most important concern. However whenever these idiosyncrasies can be removed without compromising those, they should be.

### Dynamic Class Loading
This project makes extensive use of Classloaders. This can make it slightly more difficult to debug / statically analyze. Critical usecases are called out here.

#### Operators / Modules
The ClassLoader is used to load both standard modules and user created modules. The standard modules can be found here:
- [src/tlc2/module](../src/tlc2/module)
- [src/tla2sany/StandardModules](../src/tla2sany/StandardModules)

The [SimpleFilenameToStream](../src/util/SimpleFilenameToStream.java) class is used to read in this information, and contains the logic about standard module directories. It is where the ClassLoader is used. [TLAClass](../src/tlc2/tool/impl/TLAClass.java) is also used for a similar purpose, used to loader certain built in classes.

The classpath of the created jar explicitly includes the CommunityModules such that they can be loaded if available.
```
CommunityModules-deps.jar CommunityModules.jar
```

Users can also create custom operators and modules and load them similarly.

The methods are invoked with:
``` java
mh.invoke
mh.invokeExplict
```

And this is done in a small number of locations:
[MethodValue](../src/tlc2/value/impl/MethodValue.java)
[CallableValue](../src/tlc2/value/impl/CallableValue.java)
[PriorityEvaluatingValue](../src/tlc2/value/impl/PriorityEvaluatingValue.java)


#### FPSet Selection

FPSets are dynamically selected using a system property and loaded with a ClassLoader in the [FPSetFactory](../src/tlc2/tool/fp/FPSetFactory.java).

#### Misc
- [TLCWorker](../src/tlc2/tool/distributed/TLCWorker.java): Used to load certain sun class dependencies if available.
- [BlockSelectorFactory](../src/tlc2/tool/distributed/selector/BlockSelectorFactory.java): Used to modularity load a custom BlockSelectorFactory.
- [TLCRuntime](../src/util/TLCRuntime.java): Used to get processId

### Notable Mutable Static State
The original codebase was written with the intention of being run from the command line only.

There is a significant amount of static state. While much has been removed
- [util/UniqueString.java](../src/util/UniqueString.java):
- [util/ToolIO.java](../src/util/ToolIO.java): Used for 
- [tlc2/TLCGlobals.java](../src/tlc2/TLCGlobals.java):

### Testing Brittleness

The end to end test suite is a very powerful tool of the project. It does have a reliance on the execution occurring in a very precise order. There are certain race conditions in the codebase that can cause some inconsistency in execution statistics, even while providing correct behavior. This can cause some tests to fail. Additionally, there are some race condition bugs. Additonally. It is not always easy to determine which case it falls into, and so categorizing / fixing these test cases should lead either codebase or test suite improvements. 

#### Independently Run Tests

In order to allow tests to be independently run, we add one of the following tags depending on whether it is a standard test or a TTraceTest

``` java
@Category(IndependentlyRunTest.class)
@Category(IndependentlyRunTTraceTest.class)
```

In general, these should be used sparingly, and instead if a test fails when run with others, the root cause should be discovered and fixed.

#### Unique String ordering reliance

As mentioned above, unique strings replace strings with a consistent integer token for faster comparison. That token is monotonically increasing from when the unique string is generated. When comparing unique strings, it compares the tokens, meaning the ordering of the UniqueString based collection is dependant on the ordering of the creation of strings. This can break tests that hardcode the ordering of the result output when they are not run in isolation. This isn't necessarily a fundamental problem with the system, as the output is consistent based on TLA+ semantics which does not differ based on order. 

The tests that fail for this reason are marked as independent tests, but grouped under 

``` xml
<id>unique-string-conflicts</id>
```

in [pom.xml](../pom.xml). Their reason for failure is known.

#### Debugger Tests
The AttachedDebugger currently only terminates on process exit. For that reason, all debugger tests are marked with the annotation below, and run as independent processes.

``` java
@Category(DebuggerTest.class)
```

### Primitive Versions of Standard Data Structures

The standard collections in the Java standard library store only objects. Some custom collections are required that can store and/or be indexed by primitives. These are needed for performance reasons.
- [LongVec](../src/tlc2/util/LongVec.java)
- [IntStack](../src/tlc2/util/IntStack.java)
- [SetOfLong](../src/tlc2/util/SetOfLong.java)
- [ObjLongTable](../src/tlc2/util/ObjLongTable.java)
- [LongObjTable](../src/tlc2/util/LongObjTable.java)

> Note: There may be more not listed here, but ideally they should be added.

### Unchecked Casting
As a language interpreter, there are a number of Abstract Syntax Tree node types. In many cases, functions use unchecked casts to resolve these node types, often after using if statements to check the nodes type.

To find all the classes / functions that do this, search for:
```
@SuppressWarnings("unchecked")
```

Whenever possible unchecked casts should be replaced with [pattern matching instanceof](https://docs.oracle.com/en/java/javase/17/language/pattern-matching-instanceof-operator.html). This generally is a good fit for most of the code in the codebase.

### Dead Code
This project was initiated prior to "good" version control. Therefore modern anti-patterns such as commenting out code and leaving unused methods, classes, etc have propagated. Significant amounts of dead code have been removed. Because of the use of reflection / classloaders, static analysis tools may indicate certain items are unused when they are actually depended on. Dead code removal needs to be done in conjunction with testing and exploration.

#### Acceptable Dead Code
A certain amount of dead code may have explanatory purpose.
- Standard methods implemented on data structures: ideally they should be tested, but some are not.
- Semantic variables / properties that are set appropriately but unread: They serve as a form of comment. Misleading examples of these should be removed.
- Small amounts of inline, commented out code that changes particular functionality or configures the codebase.
- Tested classes that implement used interfaces, where the class is not currently used: These still have explanatory purpose. 

Any of this code should be removed when it loses relevance or accuracy.

#### Dead Code to be Removed
- Commented out methods
- Orphan classes
- Large amounts of inline commented out code without sufficient explanatory power
- Unused, untested, non-standard methods: Version control can be used if they are needed, but they add confusion and may be broken


### Inconsistent Formatting
The formatting of certain classes is inconsistent and doesn't work well with modern IDEs. Ideally an autoformatter would be run on the codebase to fix this. However, as this is a fork of the primary codebase, it is left unrun to allow better diffs with the upstream repo.       

### JMX / Eclipse Integrations
This project was initially developed as an Eclipse project, so it includes a number of Eclipse libraries and technologies. Most of them integrate rather seamlessly as dependencies, while enabling specialized diagnostic functionality for Eclipse.

The project has [AspectJ](https://en.wikipedia.org/wiki/AspectJ) source that can be compiled in for additional diagnostics. It is also required for Long Tests to pass. The sources are located in [src-aspectj](../src-aspectj).

Additionally this project uses Java Management Extensions for diagnostic purposes. They are always used an can be a source of memory leaks. 


### Java Pathfinder
There are java pathfinder tests in the project. Sources are located in [test-verify](../test-verify/). Additional information on these tests can be found in [test-verify/README](../test-verify/README.md).