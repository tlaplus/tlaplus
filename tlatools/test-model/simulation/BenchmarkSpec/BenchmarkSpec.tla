------------------------------ MODULE BenchmarkSpec ------------------------------
EXTENDS Integers, Sequences

\*
\* This spec produces a state space with a simple tree-like structure. The maximum depth and branching
\* factor of the state space tree can be controlled by setting the constant values of the spec. The goal
\* is to give a spec whose state space structure is easily understandable and controllable, for the sake
\* of running performance and/or correctness tests of TLC.
\*

VARIABLE hist

Init == hist = <<>>

CONSTANTS Depth, BranchingFactor
    
Next ==
    \E e \in 1..BranchingFactor :
    hist' = Append(hist, e)    

Spec == Init /\ [][Next]_<<hist>>

Constraint == Len(hist) < Depth

\* An arbitrary state of max length. It's just a sequence filled with all 1's.
Inv == hist # [i \in 1..Depth |-> 1]

=============================================================================