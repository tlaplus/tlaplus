List of projects to extend/improve TLA+, TLC, TLAPS or the Toolbox
==================================================================

Please also consult the [issues tracker](https://github.com/tlaplus/tlaplus/issues) if you want to get started with contributing to TLA+. The items listed here likely fall in the range of man-months.

TLC model checker
-----------------
#### ([In Progress](https://bitbucket.org/parvmor/tarjanconcurrentscc/)) Concurrent search for strongly connected components (difficulty: high) (skills: Java, TLA+)
One part of TLC's procedure to check liveness properties, is to find the liveness graph's [strongly connected components](https://en.wikipedia.org/wiki/Strongly_connected_component) (SCC). TLC's implementation uses [Tarjan's](https://en.wikipedia.org/wiki/Strongly_connected_component) canonical solution to this problem. Tarjan's algorithm is a sequential algorithm that runs in linear time. While the time complexity is acceptable, its sequential nature causes TLC's liveness checking not to scale. Recently, concurrent variants of the algorithm have been proposed and studied in the scope of other model checkers ([Multi-Core On-The-Fly SCC Decomposition](https://github.com/utwente-fmt/ppopp16) & [Concurrent On-the-Fly SCC Detection for Automata-Based Model Checking with Fairness Assumption](http://ieeexplore.ieee.org/document/7816578/)). This work will require writing a TLA+ specification and ideally a formal proof of the algorithm's correctness.

#### Liveness checking under symmetry (difficulty: high) (skills: Java, TLA+)
[Symmetry reduction](http://www.cs.cmu.edu/~emc/papers/Conference%20Papers/Symmetry%20Reductions%20in%20Model%20Checking.pdf) techniques can significantly reduce the size of the state graph generated and checked by TLC. For safety checking, symmetry reduction is well studied and has long been implemented in TLC. TLC's liveness checking procedure however, can fail to find property violations if symmetry is declared. Yet, there is no reason why symmetry reduction cannot be applied to liveness checking. This work will require writing a TLA+ specification and ideally a formal proof of the algorithm's correctness.

#### TLC error reporting 2.0 (difficulty: moderate) (skills: Java)
TLC can only check a subset of TLA+ specifications. This subset is left implicit and a user might use language constructs and/or models that cause TLC to fail. Not infrequently, it comes up with the very helpful report “null”. To lower to barrier to learning TLA+, TLC error reporting has to better guide a user.

#### Improved runtime API for TLC (difficulty: moderate) (skills: Java)
The TLC process can be long running. It possibly runs for days, weeks or months. Today, the Toolbox interfaces with the TLC process via the command line. The Toolbox parses TLC's output and visualizes it in its UI. This is a brittle and read-only interface. Instead, communication should be done via a bidirectional network API such as RMI, JMX or REST. A network interface would even allow users to inspect and control remotely running TLC instances, e.g. those running in the cloud started through [cloud-based distributed TLC](https://tla.msr-inria.inria.fr/tlatoolbox/doc/cloudtlc/index.html). A network interface is likely to require some sort of persistence mechanism to store model runs. Persistence of model runs is trivially possible with today's text based solution. Desirable user stories are:
 - Pause/Resume TLC
 - Reduce/Increase number workers
 - Trigger checkpoints and gracefully terminate
 - Trigger liveness checking
 - Inspection hatch to see states currently being generated
 - Metrics overall and for fingerprint set, state queue, trace
 - ...
 

TLAPS
-----
#### Automatic expansion of operator definitions (difficulty: moderate) (skills: OCaml)

TLAPS currently relies on the user to indicate which operator definitions should be expanded before calling the back-end provers. Forgetting to expand an operator may make an obligation unprovable, expanding too many operators may result in a search space too big for the back-end to handle. The objective of this work would be to automatically detect which definitions have to be expanded, based on iterative deepening and possibly heuristics on the occurrences of operators in the context. The method could return the list of expanded operators so that it can be inserted in the proof, eschewing the need for repeating the search when the proof is rerun. Doing so requires modifying the proof manager but not the individual back-end interfaces.

#### SMT support for reasoning about regular expressions (difficulty: moderate to high) (skills: OCaml, SMT, TLA+)

Reasoning about TLA+ sequences currently mainly relies on the lemmas provided in the module SequenceTheorems and therefore comes with very little automation. Certain SMT solvers including [Z3](https://sites.google.com/site/z3strsolver/) and [CVC4](https://github.com/CVC4/CVC4) include support for reasoning about strings and regular expressions. Integrating these capabilities in TLAPS would be useful, for example when reasoning about the contents of message channels in distributed algorithms. Doing so will require extending the SMT backend of TLAPS, including its underlying type checker for recognizing regular expressions, represented using custom TLA+ operators.

#### Generate counter-examples for invalid proof obligations (difficulty: moderate to high) (skills: OCaml, TLA+)

Most conjectures that users attempt to prove during proof development are in fact not valid. For example, hypotheses needed to prove a step are not provided to the prover, the invariant may not be strong enough etc. When this is the case, the back-end provers time out but do not provide any useful information to the user. The objective of this work is to connect a model generator such as [Nunchaku](https://github.com/nunchaku-inria/nunchaku) to TLAPS that could provide an explanation to the user why the proof obligation is not valid. The main difficulty will be defining a translation from a useful sublanguage of TLA+ set-theoretic expressions to the input language of Nunchaku, which resembles a functional programming language.

#### Warning about unexpanded definitions (difficulty: moderate) (skills: OCaml, TLA+)

A common reason for a proof not to succeed is the failure to tell the prover to expand a definition that needs to be expanded (see section 6.1 of [Proving Safety Properties](https://lamport.azurewebsites.net/tla/proving-safety.pdf) for an example).  In some cases, simple heuristics could indicate that a definition needs to be expanded--for example, if a goal contains a symbol that does not appear in any formula being used to prove it.  The objective is to find and implement such heuristics in a command that the user can invoke to suggest what definitions may need to be expanded.  We believe that this would be an easy way to save users a lot of--especially beginning users.

TLA Toolbox
-----------
#### Port Toolbox to e4 (difficulty: easy) (skills: Java, Eclipse)
[e4](http://www.vogella.com/tutorials/EclipseRCP/article.html) represents the newest programming model for Eclipse RCP applications. e4 provides higher flexibility while simultaneously reducing boilerplate code. The TLA Toolbox has been implemented on top of Eclipse RCP 3.x and thus is more complex than it has to.

#### Add support for Google Compute to Cloud TLC (difficulty: easy) (skills: jclouds, Linux)
The Toolbox can launch Azure and Amazon EC2 instances to run model checking in the cloud. The Toolbox interfaces with clouds via the [jclouds](https://jclouds.apache.org/) toolkit. jclouds has support for Google Compute, but https://github.com/tlaplus/tlaplus/blob/master/org.lamport.tla.toolbox.jclouds/src/org/lamport/tla/toolbox/jcloud/CloudDistributedTLCJob.java has to be enhanced to support Google Compute.

#### Add support for x1 instances to jclouds (difficulty: easy) (skills: jclouds)
We raised an [enhancement request for the jclouds toolkit](https://issues.apache.org/jira/browse/JCLOUDS-1339) to add support for Amazon's largest compute instances [(x1e.32xlarge, x1.32xlarge, x1.16xlarge)](https://aws.amazon.com/ec2/instance-types/x1/).

#### Finish Unicode support (difficulty: easy) (skills: Eclipse, SANY)
A few [outstanding issues](https://github.com/tlaplus/tlaplus/issues?q=is%3Aissue+is%3Aopen+label%3AUnicode) prevent the integration of the Unicode support into the Toolbox. In addition to the open issues, adding unit tests would be welcomed. A [nightly/ci Jenkins build](https://tla.msr-inria.inria.fr/build/job/M-HEAD-pron-unicode-Toolbox.product.standalone/) is available.

TLA+ Tools
----------
#### Pretty Print to HTML (difficulty: easy) (skills: Java, HTML)
TLA+ has a great pretty-printer to TeX (`tla2tex`), but HTML is becoming a de-facto document standard, especially for content shared online. HTML also has other advantages, such as the ability to automatically add hyperlinks from symbols to their definitions, and allow for collapsing and expanding proofs. The existing `tla2tex` code already contains most of the necessary parsing and typesetting pre-processing (like alignment), and could serve as a basis for an HTML pretty-printer. A [prototype already exists](https://github.com/tlaplus/tlaplus/issues/146).

Documentation and Code Quality
------------------------------
The TLA+ source code was written by multiple people over many years, so it has cosmetic problems that are distracting to new contributors. **In general, we are not interested in cosmetic or stylistic improvements unless they also fix a concrete issue.** Large refactors carry a big risk of introducing new defects, and we have rejected well-intentioned refactors in the past because they are too large or risky to review.

However, we are happy to accept small, easy-to-review changes that incrementally improve the TLA+ toolbox and tools.  Below are a few meaningful ways to improve TLA+'s documentation and code quality.

#### Improve Internal Documentation (difficulty: easy) (skills: technical writing)
The TLA+ [internal documentation for developers](https://github.com/tlaplus/tlaplus/blob/master/DEVELOPING.md) is limited. Improving this documentation would make it much easier for new contributors to get started.

#### Improve Test Coverage (difficulty: moderate) (skills: Java)
While the TLA+ tools have good test coverage, we would much prefer them to have _great_ test coverage. This is a low-risk activity that any developer can help with.

#### Remove Uses of Global Mutable Variables (difficulty: high) (skills: Java) (low priority)
TLC cannot be easily used as a library in other projects because it makes extensive use of global mutable variables. This is not a problem for the normal use case; TLC has always been intended to run as an isolated process, not as a library. Using a separate process is a deliberate choice and a strength: the operating system provides isolation in case TLC runs out of memory and crashes. However, there would be real benefits to allowing TLC to be used as a library, e.g. [reducing test suite execution time](https://github.com/tlaplus/tlaplus/pull/756).

Fixing the existing uses of global variables must be undertaken carefully and incrementally. Previous efforts to do it have resulted in subtle soundness and completeness bugs.

#### Replace Custom Data Structures with Standard Java Collections (difficulty: moderate) (skills: Java) (low priority)
The TLA+ tools have handwritten implementations of many now-standard collection classes, such as `tla2sany.utilities.Vector` and `tlc2.util.Vect`, which duplicate the functionality of `java.util.ArrayList`. Replacing the handwritten ones with the standard types would have multiple benefits, including reducing our maintenance burden, reducing the size of the compiled tools JAR, and eliminating latent bugs. Note however that there are [subtle differences](https://github.com/tlaplus/tlaplus/pull/328#issuecomment-542160722) between the handwritten implementations and the standard ones that must be accounted for.
