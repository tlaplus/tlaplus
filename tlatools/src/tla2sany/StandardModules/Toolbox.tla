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

_TEPosition == 
    IF TLCGet("level") >= _TETraceLength
       THEN _TETraceLength
       ELSE TLCGet("level") + 1

=============================================================================
