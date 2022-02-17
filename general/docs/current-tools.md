# Current Versions of the TLA+ Tools

This document describes differences between the descriptions of the TLA+ tools in the book [_Specifying Systems_](https://lamport.azurewebsites.net/tla/book.html) and the currently released versions. References are to the version of the book currently available on the web. The book and this document do not describe the features provided by the [TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html) for using the tools. They are described by the Toolbox's help pages and the [TLA+ Hyperbook](https://lamport.azurewebsites.net/tla/hyperbook.html).

## SANY (The Semantic Analyzer)

The current release of SANY has no known limitations.

## TLC

### Limitations

Below are all the known ways in which the current release of TLC differs from the version described in the book.

TLC doesn't implement the `\cdot` (action composition) operator.

TLC cannot handle definitions that comes from a parametrized instantiation. For example, suppose a module *M*, which has the variable parameter *x*, defines the specification *Spec*. If you define *ISpec* by

```tla
IM(x) == INSTANCE M
ISpec == IM(xbar)!Spec
```

then TLC will not be able to check the property ISpec. However, TLC will be able to check ISpec if it's defined in the following equivalent way:

```tla
IM == INSTANCE M WITH x <- xbar
ISpec == IM!Spec
```

TLC cannot handle natural numbers greater than 2<sup>31</sup> - 1.

### Additional Features

#### Enhanced Replacement

Most users now run TLC from the Toolbox, where overriding of definitions is performed in the **Definition Override** section of the model's **Advanced Model Options** page. Search for "override" in the Toolbox's Help pages.

When running TLC from the command line, definition overriding is specified by the configuration file. As described in _Specifying Systems_, when running TLC on a module _M_, a replacement

```tla
foo <- bar
```

replaces *foo* by *bar* in all operators either defined in _M_ or imported into _M_ through EXTEND statements. (For example, if _M_ extends _M1_ which extends _M2_, then the replacement will occur in operators defined in _M1_ and _M2_, as well as in _M_.) It does not perform the replacement on any operators imported into _M_ by an INSTANCE statement. The replacement

```tla
foo <- [Mod] bar
```

replaces _foo_ by _bar_ in all operators defined in module _Mod_ or imported into _Mod_ through EXTEND statements. You should use this if you want the replacement to be made in a module _Mod_ that is instantiated either by the module _M_ on which TLC is being run, or by some module imported into _M_ through EXTEND statements.

An operator may be imported into the current module by multiple paths. For example, the identifier _Nat_ can be imported directly from the _Integers_ module by an EXTENDS statement or indirectly through an instantiated module, often under a different name. In that case, to redefine _Nat_ to equal 0..2, it's safest to put both of the following in the configuration file:
```tla
Nat <- 0..2
Nat <- [Integers] 0..2
```

#### Strings

TLA+ defines strings to be sequences, but the TLC implementation does not regard them as first-class sequences. The Java implementation of the _Sequences_ module has been enhanced so that `\o` and Len do what they should for strings. For example, TLC knows that `"ab" \o "c"` equals `"abc"` and that `Len("abc")` equals 3. However, Len does not work right for strings containing special characters written with `\`. (See the bottom of page 307 of the TLA+ book.)

#### New Features in the TLC Module

***TLCGet* and *TLCSet***

TLC can now read and set a special list of values while evaluating expressions. This works as follows. The _TLC_ module defines two new operators:

```tla
TLCGet(i) == CHOOSE n : TRUE
TLCSet(i, v) == TRUE
```

When TLC evaluates `TLCSet(i, v)`, for any positive integer _i_ and arbitrary value _v_, in addition to obtaining the value TRUE, it sets the *i*th element of the list to *v*. When TLC evaluates `TLCGet(i)`, the value it obtains is the current value of the *i*th element of this list. For example, when TLC evaluates the formula

```tla
/\ TLCSet(42, <<"a", 1>>)
/\ \A i \in {1, 2, 3} :
    /\ Print(TLCGet(42), TRUE)
    /\ TLCSet(42, [TLCGet(42) EXCEPT ![2] = @ + 1])
```

it prints

```tla
<< "a", 1 >> TRUE
<< "a", 2 >> TRUE
<< "a", 3 >> TRUE
```

One use of this feature is to check TLC's progress during long computations. For example, suppose TLC is evaluating a formula `\A x \in S : P` where _S_ is a large set, so it evaluates P many times. You can use _TLCGet_, _TLCSet_, and _Print_ to print something after every 1000th time TLC evaluates _P_.

As explained in the description of the _TLCEval_ operator below, you may also want to use this feature to count how many times TLC is evaluating an expression _e_. To use value number _i_ as the counter, just replace _e_ by

```tla
IF TLCSet(i, TLCGet(i) + 1) THEN e ELSE 42
```

(The ELSE expression is never evaluated.)

For certain strings *str*, the value of `TLCGet(str)` equals a number describing some aspect of TLC's current execution. Here is the meaning of `TLCGet(str)` for strings *str*.

`"generated"` The number of states generated.

`"distinct"` The number of distinct states found.

`"queue"` The number of states waiting in the queue to be processed.

`"duration"` The number of seconds elapsed since model checking began.

`"level"` The length of the path in the state graph from an initial state to
the current state.

`"diameter"` The maximum value of `TLCGet("level")` of all states examined thus far.

For the following two strings _str_, evaluating `TLCSet(str)` causes TLC to
take this action:

`"pause"` Pauses model checking.

`"exit"` Terminates model checking when all workers have finished processing their current state.

For reasons of efficiency, _TLCGet_ and _TLCSet_ behave somewhat strangely when TLC is run with multiple worker threads (using the `-workers` option). Each worker thread maintains its own individual copy of the list of values on which it evaluates _TLCGet_ and _TLCSet_. The worker threads are activated only after the computation and invariance checking of the initial states. Before then, evaluating `TLCSet(i, v)` sets the element _i_ of the list maintained by all threads. Thus, the lists of all the worker threads can be initialized by putting the appropriate _TLCSet_ expression in an ASSUME expression or in the initial predicate.

To allow information collected with _TLCGet_ and _TLCSet_ to be reported when TLC finishes, TLC now allows the `cfg` file to contain the statement

```tla
POSTCONDITION Op
```

where _Op_ is a constant-level operator with no arguments defined in the spec or the model. After executing the model, TLC evaluates the operator _Op_.

**TLCEval**

TLC often uses lazy evaluation. For example, it may not enumerate the elements of a set of the form `{x \in T : P(x)}` unless it has to; and it doesn't have to if it only needs to check if an element _e_ is in that set. (TLC can do that by evaluating `x \in T` and `P(e)`.) TLC uses heuristics to determine when it should completely evaluate an expression. Those heuristics work well most of the time. However, sometimes lazy evaluation can result in the expression ultimately being evaluated multiple times instead of just once. This can especially be a problem when evaluating a recursively defined operator.

You can solve this problem with the _TLCEval_ operator. The _TLC_ module defines the operator _TLCEval_ by

```tla
TLCEval(x) == x
```

TLC evaluates the expression `TLCEval(e)` by completely evaluating _e_.

If TLC is taking a long time to evaluate something, you can check if lazy evaluation is the source of the problem by using the _TLC_ module's _TLCSet_ and _TLCGet_ operators to count how many times expressions are being evaluated, as described above.

**Any**

Originally, TLA+ allowed only functions to be defined recursively. One problem with this was that it's sometimes a nuisance to have to write the domain of the function _f_. There were two reasons it might be a nuisance: the domain might be complicated, or TLC might spend a lot of time when evaluating `f[x]` in checking that _x_ is in the domain of _f_. The operator _Any_ was added to the TLC module as a hack to work around this problem. With the introduction of recursive operator definitions, this problem disappeared and there is no reason to use _Any_. However, it is retained for backwards compatibility. Here is its description.

The definition of the constant _Any_ doesn't matter. This constant has the special property that, for any value _v_, TLC evaluates the expression `v \in Any` to equal TRUE. You can avoid having to specify the domain in a function definition by letting the domain be _Any_.

The use of _Any_ sounds dangerous, since it acts like the set of all sets and raises the specter of Russell's paradox. However, suppose a specification uses _Any_ only in function definitions without doing anything sneaky. Then for any execution of TLC that terminates successfully, there is a finite set that can be substituted for _Any_ that yields the same execution of TLC. That set is just the set of all values _v_ for which TLC evaluates `v \in Any` during its execution. However, unrestricted use of _Any_ can get TLC to verify incorrect modules. For example, it will evaluate `Any \in Any` to equal TRUE, even though it equals false for any actual set _Any_.

You should not use _Any_ in an actual specification; it is intended only to help in using TLC. In the actual specification, you should write the definition like

```tla
f[x \in Dom] == ...
```

where the domain _Dom_ is either defined or declared as a constant parameter. In the configuration file, you can tell TLC to substitute _Any_ for _Dom_.

**PrintT**

The TLC module defines

```tla
PrintT(out) == TRUE
```

However, evaluating `PrintT(out)` causes TLC to print the value of _out_. This allows you to eliminate the annoying "TRUE" produced by evaluating `Print(out, TRUE)`.

**RandomElement**

The TLC module defines

```tla
RandomElement(S) == CHOOSE x \in S : TRUE
```

so `RandomElement(S)` is an arbitrarily chosen element of the set _S_. However, contrary to what the definition says, TLC actually makes an independent choice every time it evaluates `RandomElement(S)`, so it could evaluate

```tla
RandomElement(S) = RandomElement(S)
```

to equal FALSE.

When TLC evaluates `RandomElement(S)`, it chooses the element of _S_ pseudo-randomly with a uniform probability distribution. This feature was added to enable the computation of statistical properties of a specification's executions by running TLC in simulation mode. We haven't had a chance to do this yet; let us know if you try it.

**ToString**

TLA+ defines `ToString(v)` to be an arbitrarily chosen string whose value depends on _v_. TLC evaluates it to be a string that is the TLA+ expression whose value equals the value of _v_. By using _ToString_ and string concatenation `\o` in the argument of the _Print_ or _PrintT_, you can get TLC to print nicer-looking output than it ordinarily does.

#### The *Randomization* Module

The _RandomElement_ operator of the TLC module computes all the elements of its argument set before choosing one. This makes it unusable for very large sets. The _Randomization_ module provides operators that can be used to randomly choose a subset of a very, very large set (including a subset with a single element).

#### Typed Model Values

One way that TLC finds bugs is by reporting an error if it tries to compare two incomparable values&mdash;for example, a string and a set. The use of model values can cause TLC to miss bugs because it will compare a model value to any value without complaining (finding it unequal to anything but itself). Typed model values have been introduced to solve this problem.

For any character &tau;, a model value whose name begins with the two-character string "&tau;\_" is defined to have type &tau;. For example, the model value _x\_1_ has type _x_. Any other model value is untyped. TLC treats untyped model values as before, being willing to compare them to anything. However it reports an error if it tries to compare a typed model value to anything other than a model value of the same type or an untyped model value. Thus, TLC will find the model value _x_1_ unequal to the model values _x_ab2_ and _none_, but will report an error if it tries to compare _x\_1_ to _a\_1_.

#### Overriding Modules

TLC permits definitions from a module _M_ to be overridden by Java code in a file _M_.class. This is used primarily for implementing standard modules, but it can be applied to any module if you are willing to write the appropriate Java code. You can put the `.class` file in the same folder/directory as the module's `.tla` file. The files in the `tlc2.module` package contain examples of how the Java code is written.

### Command-Line Options

Several command-line options have been added to TLC since _Specifying Systems_ was written. Moreover, the book did not list all the options available then. Most users now run TLC from the Toolbox, which provides a convenient way to specify the most commonly used TLC options; few people will use command-line options. However, since there is no conveniently available list of all those options, they are presented here. A parameter _file_ is the path name of a file&mdash;either an absolute path or one relative to the directory from which TLC is run. Similarly, a parameter _dir_ is the absolute or relative path name of a directory.

`-aril` _num_
Adjusts the seed for random simulation. (See page 251 of the book.) It defaults to 0 if not specified.

`-checkpoint` _num_
Tells TLC to take a checkpoint every _num_ minutes. The default is 30.

`-cleanup`
Cleans up the states directory, removing all existing checkpoint files.

`-config` _file_
Provides the configuration (`.cfg`) file. Defaults to `spec.cfg` if not provided.

`-continue`
Normally, TLC stops when it finds a violation of a property it is checking. This option tells TLC to continue running when it finds a violation of a safety property. (It always stops when a liveness property is violated.) This option cannot be used from the Toolbox.

`-coverage` _num_
This option tells TLC to print coverage information every _num_ minutes. Without the option, TLC prints no coverage information.

`-deadlock`
This tells TLC not to check for deadlock.

`-debug`
Tells TLC to print information useful for debugging its own code.

`-depth` _num_
Specifies the depth (number of steps) of a random simulation. Without this option, the default depth is 100.

`-dfid` _num_
Directs TLC to do depth-first model checking with iterative deepening, beginning with initial depth _num_.

`-postCondition mod!oper`
Evaluates the given (constant-level) operator _oper_ in the TLA+ module _mod_ at the end of model-checking.

Example: `-postCondition MyModule!SomePostCondition`.

`-difftrace`
Tells TLC to show only the differences between successive states when printing an error trace. Otherwise, it prints the full state descriptions.

`-dumpTrace` _format file_
In case of a property violation, formats the TLA+ error trace to the given format _format_ and dumps the output to the specified file _file_. The file _file_ is relative to the same directory as the main spec.  At the time of writing, TLC supports the `tla` and the `json` formats.  To dump to multiple formats, the -dumpTrace parameter may appear multiple times.  The git commits [1eb815620](https://github.com/tlaplus/tlaplus/commit/1eb815620dedc696a5a637944853129595c47216) and [386eaa19f](https://github.com/tlaplus/tlaplus/commit/386eaa19f4d610781a79c95730638ba193cec614) show that adding new formats is easy.

Example: `-dumpTrace tla file.tla -dumpTrace json file.json`.

`-dump` _format file_
The _format_ parameter can be omitted, or it can be a comma-separated list beginning with `dot` that may also contain one or both of the items `colorize` and `actionlabels`. If _format_ is omitted, TLC writes a list of all reachable states, described by TLA+ formulas, on _file_. Otherwise, TLC writes the state graph in dot format, the input format of the GraphViz program for displaying graphs. The parameter `colorize` indicates that state transitions should be colored according to the action generating the transition, and `actionlabels` indicates that they should be labeled with the name of the action. 

Example: `-dump dot,colorize,actionlabels file.dot`.

`-fp` _num_
TLC's state fingerprinting algorithm uses one of a list of irreducible polynomials, numbered 0 through 130. This option tells it to use polynomial number _num_. Through release version 1.5.7 of the tools, The default is to used number 0. In later versions the default will be to use a randomly chosen one.

`-fpbits` _num_
Directs TLC to partition its fingerprint set into 2<sup>_num_</sup> separate disk files. (On some systems, using multiple files can improve efficiency of reading and writing fingerprints when they don't fit in memory.) The default value of _num_ is 0.

`-fpmem` _num_
Tells TLC how much memory to use to store the fingerprints of found states. If _num_ is an integer, it specifies the number of megabytes; if it's a fraction between 0 and 1, it specifies that fraction of the memory size.The default value of _num_ is .25.

`-gzip`
This tells TLC to compress the state queue when writing it to disk.

`-help`
Causes TLC to output a help message containing the information in this
section and stop.

`-lncheck` _param_
If this is omitted or _param_ equals `default`, TLC performs liveness checking periodically, roughly whenever the number of distinct states it finds increases by 10%. If _param_ equals `final`, TLC does liveness checking only after it has computed the complete state graph.

`-maxSetSize` _num_
The cardinality of the largest set that TLC can handle. TLC reports an error if it tries to compute a set containing more elements. It defaults to 1000000 if this option is not specified.

`-metadir` _dir_
Tells TLC to store its metadata in the directory given by _dir_. Without this option, the default is to use the `states` subfolder of the directory containing the specification file.

`-modelcheck`
Tells TLC to run in model checking mode, which is the default.

`-nowarning`
Tells TLC not to issue any warnings. Otherwise, TLC reports all warnings. (A warning indicates a possible error, but does not cause TLC to stop.)

`-recover` _dir_
Recover from the checkpoint found in the directory specified by _dir_. If not specified, TLC performs a fresh execution of the model.

`-seed` _num_
Provide the seed for the pseudo-random number generator used for random simulation. Defaults to a randomly chosen seed if not specified.

`-simulate` file=_pname_ num=_num_ stats=(basic|full) 
This tells TLC to run in simulation mode. If the `file` argument is present, then TLC writes each trace it finds to the file whose name, including complete directory path, is _pname_. If the `num` argument is present, then _num_ is the number of behaviors to generate. If the `stats` argument is present, you must select either basic mode or full mode. Both modes generate a DOT file representing an action graph named in the `<spec>_actions.dot` format. Basic mode generates an action graph where nodes are actions, solid edges are seen transitions, and dashed edges are unseen transitions during the simulation. Full mode also generates an action graph, but now there are clusters of actions (actions might appear more than once) representing interactions between actions with parameters, for example actions A(1) points to A(2) which points to B(1), whereas in basic mode you'd only see A points to B. 
Either or all arguments may be omitted; if more than one is present, they must be separated by a comma. 

Example: ```-simulate file=trace.txt,num=100,stats=full```

`-terse`
Tells TLA not to expand values in the output produced by Print and PrintT. If not specified, the values are expanded.

`-tool`
Tells TLC to print its output in a format to be read by a program such as the Toolbox.

`-userFile` _file_
It tells TLC to write output produced by the Print and PrintT operators in file.

`-view`
If the configuration file specifies a VIEW, then this option tells TLC to apply that view to the states when printing an error trace.

`-workers` _num_ or `auto`
Specifies the number of TLC worker threads, where `auto` means to use as many threads as there are cores on the computer. Without this option, TLC uses only a single worker thread.

### Java System Properties

In addition to command line options, TLC also uses several Java system properties to choose between different algorithms for certain tasks. You set a Java system property by adding it to TLC's command line via `java -Dkey=value -jar tla2tools.jar ...`.  In particular, the following properties can improve performance when TLC is run with many worker on a large number of cores.

`tlc2.tool.fp.FPSet.impl`
Defines which fingerprint set implementation to use. For better many-core performance, pass `-Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet`.

`tlc2.tool.ModelChecker.BAQueue`
If run with `-Dtlc2.tool.ModelChecker.BAQueue=true`, TLC will use the `ByteArrayQueue`, a prototype implementation that increases many-core throughput by reducing the critical section of the queue of unseen states.


## TLATEX
### Bugs

There are some bugs in TLATEX that cause an occasional misalignment in the output. TLATEX also doesn't do a good job of formatting CASE statements. We would appreciate suggestions for how case statements should be formatted.

### Inserting TLA+ in a LATEX Document

There is a version of TLATEX for typesetting pieces of TLA+ specifications in a LATEX document. In the `.tex` file, you put

```
\begin{tla} 
An arbitrary portion of a TLA+ specification
\end{tla}
```

Running TLATEX on the file inserts a `tlatex` environment immediately after this `tla` environment that contains the typeset version of that portion of the TLA+ specification, replacing any previous version of the `tlatex` environment.

There are analogous LATEX `pcal` and `ppcal` environments for formatting PlusCal code. The `pcal` environment is for code written in PlusCal's C-syntax; the `ppcal` environment is for P-syntax code.

You run this version of TLATEX with the command `java tlatex.TeX`. Executing

```
java tlatex.TeX -info
```

will type out reasonably detailed directions on using the program.

## PlusCal

The PlusCal manual describes the current release of the PlusCal translator. It can be found [here.](https://lamport.azurewebsites.net/tla/learning.html)
