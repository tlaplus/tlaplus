--------------------------- MODULE TLCGetNonDeterminism ----------------------------
EXTENDS Integers, TLC

\* A monotonic counter:

VARIABLES x,y

Init == /\ TLCSet(1, 0)
        /\ x = 0
        /\ y = TLCGet(1)

\* Replacing "TLCGet(1) + 1" with "x'" does not trigger the TLC bug.
\* "x'" is clearly defined but TLCGet(1) returns the local value of 
\* a non-deterministically chosen worker from the set of TLC workers
\* (the local values are inconsistent and depend on worker threading).
\*
\* In other words, this next-state relation does not correspond to a
\* single behavior <x=1,y=1>, <x=2,y=2>, <x=3,y=3> but to a set of
\* behaviors where the value of y \in 1..3 depends on the actual
\* worker schedule. E.g. with three workers, the behavior might be:
\* <x=1,y=1-a>, <x=2,y=1-b>, <x=3,y=1-c> with 1-a being the local value
\* of worker a, 1-b the local value of worker b, ...
Next == /\ x < 3
        /\ TLCSet(1, TLCGet(1) + 1) 
        /\ x' = x + 1
        /\ y' = TLCGet(1)

\* This bug surfaces at a later stage, when TLC re-creates the error
\* trace for the violation of Prop below:
\*   Error: TLC threw an unexpected exception.
\*   This was probably caused by an error in the spec or model.
\*   The error occurred when TLC was checking liveness.
\*   The exception was a tlc2.tool.EvalException
\*   : Failed to recover the next state from its fingerprint.
\*
\* During error trace re-creation (where TLC re-creates the actual states
\* from a path in the fingerprint graph, TLC always runs with a single worker.
\* Consequently, it always create the expected <x=1,y=1>, <x=2,y=2>, <x=3,y=3>
\* behavior.  This behavior however gets rejected because the fingerprints
\* in the path do not match the fingerprint of the re-created states.

------------------------------------------------------------------------------

\* Force an arbitrary liveness violation by allowing
\* x to go up to 3 but expect x to remain -lt 3 forever.
Prop == <>[](x < 3)

=============================================================================
