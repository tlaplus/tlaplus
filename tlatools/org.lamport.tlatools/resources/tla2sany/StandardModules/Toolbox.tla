----------------------------- MODULE Toolbox --------------------------------
(***************************************************************************)
(*                                                                         *)
(***************************************************************************)
LOCAL INSTANCE Naturals   \* a + b
LOCAL INSTANCE FiniteSets \* Cardinality
LOCAL INSTANCE TLC        \* TLCGet

-----------------------------------------------------------------------------

(* Trace Exploration *)

_TETrace ==
    CHOOSE f \in [ (Nat \ {0}) -> STRING ] : TRUE

LOCAL _TETraceLength == Cardinality(DOMAIN _TETrace)

\* When evaluated as part of a TLC ALIAS expression, `_TEPosition` should be
\* redefined as `TLCGet("level"), or replace with `TLCGet(level)` right away.
\* The definition below accounts for several "peculiarities" of the
\* Toolbox's trace exploration.
_TEPosition == 
    IF TLCGet("level") >= _TETraceLength
       THEN _TETraceLength
       ELSE IF TLCGet("level") = 0 THEN 1 ELSE TLCGet("level")

=============================================================================
