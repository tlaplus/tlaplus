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
  /\ TLCGet("spec") = 
				[ impliedinits |-> {},
				  invariants |-> {},
				  impliedtemporals |-> {},
				  temporals |-> {},
				  actions |->
				      { [ name |-> "Next",
				          location |->
				              [ beginLine |-> 31,
				                beginColumn |-> 3,
				                endLine |-> 35,
				                endColumn |-> 17,
				                module |-> "Github866" ] ] },
				  inits |->
				      { [ name |-> "Init",
				          location |->
				              [ beginLine |-> 27,
				                beginColumn |-> 3,
				                endLine |-> 27,
				                endColumn |-> 7,
				                module |-> "Github866" ] ] },
				  variables |->
				      { [ name |-> "x",
				          location |->
				              [ beginLine |-> 24,
				                beginColumn |-> 11,
				                endLine |-> 24,
				                endColumn |-> 11,
				                module |-> "Github866" ] ] },
				  actionconstraints |->
				      { [ name |-> "ActionConstraint",
				          location |->
				              [ beginLine |-> 94,
				                beginColumn |-> 1,
				                endLine |-> 94,
				                endColumn |-> 30,
				                module |-> "Github866" ] ] },
				  constraints |->
				      { [ name |-> "Constraint",
				          location |->
				              [ beginLine |-> 93,
				                beginColumn |-> 1,
				                endLine |-> 93,
				                endColumn |-> 23,
				                module |-> "Github866" ] ] } ]
				  
Constraint == x \in Nat
ActionConstraint == x' \in Nat

ASSUME TLCGet("-Dfile.separator") \in {"/", "\\"}
ASSUME TLCGet("-Dasdiftb872w7t4ergvsivc") = "-Dasdiftb872w7t4ergvsivc"
==========================================================================
---------------------------- CONFIG Github866 ----------------------------
SPECIFICATION Spec
POSTCONDITION PostCondition
CONSTRAINT Constraint
ACTION_CONSTRAINT ActionConstraint
==========================================================================
