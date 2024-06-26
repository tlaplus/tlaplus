---------------------------- MODULE Github866 ---------------------------
EXTENDS Naturals, TLC

\* Test requires at least two workers.
ASSUME TLCGet("config").worker > 1

r == 0

\* Initialize the register to a value *outside* of X.
ASSUME TLCSet(r, {0})

\* At startup, SpecProcessor evaluates X. The likelihood that two or more
\* workers will evaluate X differently is proportional to the size of the
\* input set provided to RandomElement.
X ==
  \* The value that RandomElement evaluates to has to be nested in a TLC 
  \* IValue instance that may change its internal representation during
  \* normalization/fingerprinting (see IValue#mutates). Otherwise,
  \* WorkerValue#demux becomes a no-op.
  {RandomElement(1..10000)}

-------------------------------------------------------------------------

VARIABLES x

Init ==
  x = 0

Next ==
  \* Keep going until all workers have evaluated next.
  /\ \E w \in 1..TLCGet("config").worker: 
          TLCGet("all")[r][w] = {0}
  /\ x' = x + 1
  \* Set the register value r to the worker-specific value of X.
  /\ TLCSet(r, X)

Spec ==
  Init /\ [][Next]_x

-------------------------------------------------------------------------

PostCondition ==
  /\ PrintT(TLCGet("all")[r])
  /\ \A v,w \in 1..TLCGet("config").worker:
       /\ TLCGet("all")[r][v] # {0}
       /\ TLCGet("all")[r][v] = TLCGet("all")[r][w]
       
==========================================================================
---------------------------- CONFIG Github866 ----------------------------
SPECIFICATION Spec
POSTCONDITION PostCondition
==========================================================================
