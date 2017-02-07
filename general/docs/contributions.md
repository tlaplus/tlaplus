List of projects to extend/improve TLA+, TLC, TLAPS or the Toolbox
==================================================================

TLC model checker
-----------------
#### Concurrent search for strongly connected components
One part of TLC's procedure to check liveness properties, is to find the liveness graph's [strongly connected components](https://en.wikipedia.org/wiki/Strongly_connected_component) (SCC). TLC's implementation uses [Tarjan's](https://en.wikipedia.org/wiki/Strongly_connected_component) canonical solution to this problem. Tarjan's algorithm is a sequential algorithm that runs in linear time. While the time complexity is acceptable, its sequential nature causes TLC's liveness checking not to scale. Recently, concurrent variants of the algorithm have been proposed and [studied in the scope of other model checkers](https://wwwhome.ewi.utwente.nl/~laarman/papers/scc_ppopp_2016.pdf).

#### Liveness checking under symmetry
[Symmetry reduction](http://www.cs.cmu.edu/~emc/papers/Conference%20Papers/Symmetry%20Reductions%20in%20Model%20Checking.pdf) techniques can significantly reduce the size of the state graph generated and checked by TLC. For safety checking, symmetry reduction is well studied and has long been implemented in TLC. TLC's liveness checking procedure however, can fail to find property violations if symmetry is declared. Yet, there is no reason why symmetry reduction cannot be applied to liveness checking.

#### TLC error reporting 2.0
TBD

#### Improved runtime API for TLC
The TLC process can be long running. It possibly runs for days, weeks or months. Today, the Toolbox interfaces with the TLC process via the command line. The Toolbox parses TLC's output and visualizes it in its UI. This is a brittle and read-only interface. Instead, communication should be done via a bidirectional network API such as RMI, JMX or REST. Desirable user stories are:
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
#### Port Toolbox to e4
[e4](http://www.vogella.com/tutorials/EclipseRCP/article.html) represents the newest programming model for Eclipse RCP applications. e4 provides higher flexibility while simultaneously reducing boilerplate code. The TLA Toolbox has been implemented on top of Eclipse RCP 3.x and thus is more complex than it has to. 

