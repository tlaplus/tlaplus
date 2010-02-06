--------------------------- MODULE LiveHourClock ----------------------------
(***************************************************************************)
(* This module adds the liveness condition to the hour clock specification *)
(* of module HourClock.                                                    *)
(***************************************************************************)

EXTENDS HourClock

LSpec == HC /\ WF_hr(HCnxt)
  (*************************************************************************)
  (* The specification with the liveness condition conjoined.              *)
  (*************************************************************************)

(***************************************************************************)
(* We now define some properties that LSpec satisfies.                     *)
(***************************************************************************)
AlwaysTick == []<><<HCnxt>>_hr
  (*************************************************************************)
  (* Asserts that infinitely many <<HCnxt>>_hr steps occur.                *)
  (*************************************************************************)

AllTimes == \A n \in 1..12 : []<>(hr = n)
  (*************************************************************************)
  (* Asserts that, for each time n in 1..12, hr infinitely often equals n. *)
  (*************************************************************************)

TypeInvariance == []HCini
  (*************************************************************************)
  (* The temporal formula asserting that HCini is always true.  It is      *)
  (* stated in this way to show you another way of telling TLC to check an *)
  (* invariant.                                                            *)
  (*************************************************************************)
  
-----------------------------------------------------------------------------
THEOREM  LSpec => AlwaysTick /\ AllTimes /\ TypeInvariance
=============================================================================

