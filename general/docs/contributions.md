List of projects to extend/improve TLA+, TLC, TLAPS or the Toolbox
==================================================================

Please also consult the [issues tracker](https://github.com/tlaplus/tlaplus/issues) if you want to get started with contributing to TLA+. The items listed here likely fall in the range of man-months.

TLC model checker
-----------------
#### Concurrent search for strongly connected components (difficulty: high) (skills: Java, TLA+)
One part of TLC's procedure to check liveness properties, is to find the liveness graph's [strongly connected components](https://en.wikipedia.org/wiki/Strongly_connected_component) (SCC). TLC's implementation uses [Tarjan's](https://en.wikipedia.org/wiki/Strongly_connected_component) canonical solution to this problem. Tarjan's algorithm is a sequential algorithm that runs in linear time. While the time complexity is acceptable, its sequential nature causes TLC's liveness checking not to scale. Recently, concurrent variants of the algorithm have been proposed and [studied in the scope of other model checkers](https://wwwhome.ewi.utwente.nl/~laarman/papers/scc_ppopp_2016.pdf). This work will require writing a TLA+ specification and ideally a formal proof of the algorithm's correctness.

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
TBD

TLA Toolbox
-----------
#### Port Toolbox to e4 (difficulty: easy) (skills: Java, Eclipse)
[e4](http://www.vogella.com/tutorials/EclipseRCP/article.html) represents the newest programming model for Eclipse RCP applications. e4 provides higher flexibility while simultaneously reducing boilerplate code. The TLA Toolbox has been implemented on top of Eclipse RCP 3.x and thus is more complex than it has to.

#### Package Toolbox for Debian and Fedora based Linux distributions (difficulty: easy) (skills: Eclipse, Linux)
The current Toolbox installation requires Linux users to download a zip file, to extract it and manually integrate the Toolbox into the System. Packaging the Toolbox for Debian (.deb) and Fedora (.rpm) based Linux distributions would not only simplify the installation procedure, it would also create more visible for TLA+ within the Linux community.

