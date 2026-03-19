------------------------------ MODULE Prisoners ----------------------------- 
(***************************************************************************)
(* This module specifies the solution to the following puzzle, given on    *)
(* the Car Guys NPR radio show:                                            *)
(*                                                                         *)
(*    The warden of a prison gives his prisoners the following problem.    *)
(*    There is a room in the prison with two switches, labeled A and B.    *)
(*    Each switch can be either up or down.  Every so often, the warden    *)
(*    will select a prisoner at random and take him into the room, where   *)
(*    he must flip (change the position of) exactly one of the switches.   *)
(*    The only guarantee he makes is that every prisoner will eventually   *)
(*    be brought into the room multiple times.  (More precisely, there     *)
(*    will never be a time after which some prisoner is never again        *)
(*    brought into the room.)                                              *)
(*                                                                         *)
(*    At any time, any prisoner may declare that all the prisoners have    *)
(*    been in the room at least once.  If that prisoner is right, then     *)
(*    all the prisoners go free.  If he is wrong, all the prisoners are    *)
(*    immediately executed.                                                *)
(*                                                                         *)
(*    The prisoners are allowed to decide upon a strategy, after which     *)
(*    they will not be allowed to communicate with one another.  And, of   *)
(*    course, they cannot see the room or who is being brought into it.    *)
(*    What do they do?                                                     *)
(*                                                                         *)
(* The solution presented by the Car Guys is specified below.              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS 
  Prisoner,
    (***********************************************************************)
    (* The set of all prisoners.                                           *)
    (***********************************************************************)

  Counter  
    (***********************************************************************)
    (* This is an arbitrarily chosen prisoner, who will do the necessary   *)
    (* counting.                                                           *)
    (***********************************************************************)

ASSUME 
  (*************************************************************************)
  (* We assume that the counter is a prisoner.  We also assume that there  *)
  (* is more than one prisoner.  (The problem is trivial if there is a     *)
  (* single prisoner.)                                                     *)
  (*************************************************************************)
  /\ Counter \in Prisoner
  /\ Cardinality(Prisoner) > 1

OtherPrisoner == Prisoner \ {Counter}
  (*************************************************************************)
  (* The set of all prisoners other than the counter.                      *)
  (*************************************************************************)
  
VARIABLES 
  switchAUp, switchBUp,    
    (***********************************************************************)
    (* The states of the two switches, represented by boolean-valued       *)
    (* variables.                                                          *)
    (***********************************************************************)
    
  timesSwitched,
    (***********************************************************************)
    (* For ever prisoner except the counter, timesSwitched[p] is the       *)
    (* number of times prisoner p has moved switch A up.  It is initially  *)
    (* 0 and will equal at most 2.                                         *)
    (***********************************************************************)

  count
    (***********************************************************************)
    (* The number of times the Counter has switched switch A down.         *)
    (***********************************************************************)

vars == <<switchAUp, switchBUp, timesSwitched, count>>    
  (*************************************************************************)
  (* The tuple of all variables.                                           *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We first define three state predicates.                                 *)
(***************************************************************************)
TypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant.  This is not actually part of the     *)
  (* specification.  It is added to help the reader understand the         *)
  (* specification and also because letting TLC (the model checker) check  *)
  (* that it is an invariant is a good way to debug the specification.     *)
  (*                                                                       *)
  (* Note the bound on the value of count.                                 *)
  (*************************************************************************)
  /\ switchAUp     \in BOOLEAN
  /\ switchBUp     \in BOOLEAN
  /\ timesSwitched \in [OtherPrisoner -> 0..2]
  /\ count         \in 0 .. (2 * Cardinality(Prisoner) - 1)

Init ==
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ switchAUp \in BOOLEAN
  /\ switchBUp \in BOOLEAN
  /\ timesSwitched = [i \in OtherPrisoner |-> 0]
  /\ count     = 0

Done == 
  (*************************************************************************)
  (* This is the condition that tells the counter that every other         *)
  (* prisoner has been in the room at least once.  (He will trivially know *)
  (* that he's already been in the room when this condition is true.)      *)
  (*************************************************************************)
  count = 2 * (Cardinality(Prisoner) - 1)
-----------------------------------------------------------------------------
(***************************************************************************)
(* Next come the actions performed by each prisoner when he (or she) is    *)
(* brought into the room with the switches.                                *)
(***************************************************************************)
NonCounterStep(i) ==
  (*************************************************************************)
  (* A prisoner other than the counter moves switch A up if it is down and *)
  (* if (s)he has not already moved it up two times.  Otherwise, (s)he     *)
  (* flips switch B.                                                       *)
  (*************************************************************************)
  /\ IF (~switchAUp) /\ (timesSwitched[i] < 2)
       THEN /\ switchAUp' = TRUE
            /\ timesSwitched' = [timesSwitched EXCEPT ![i] = @+1]
            /\ UNCHANGED switchBUp
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, timesSwitched>>
  /\ UNCHANGED count
       
CounterStep ==
  (*************************************************************************)
  (* If switch A is up, the counter moves it down and increments his (or   *)
  (* her) count.  Otherwise, (s)he flips switch B.                         *)
  (*************************************************************************)
  /\ IF switchAUp
       THEN /\ switchAUp' = FALSE
            /\ UNCHANGED switchBUp
            /\ count' =  count + 1
       ELSE /\ switchBUp' = ~switchBUp
            /\ UNCHANGED <<switchAUp, count>>
  /\ UNCHANGED timesSwitched

Next == 
  (*************************************************************************)
  (* The next-state relation                                               *)
  (*************************************************************************)
  \/ CounterStep 
  \/ \E i \in OtherPrisoner : NonCounterStep(i)

Fairness == 
  (*************************************************************************)
  (* This asserts that every prisoner is brought into the room infinitely  *)
  (* often.                                                                *)
  (*************************************************************************)
  /\ WF_vars(CounterStep)
  /\ \A i \in OtherPrisoner : WF_vars(NonCounterStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness
-----------------------------------------------------------------------------
Safety == 
  (*************************************************************************)
  (* This formula asserts that safety condition: that Done true implies    *)
  (* that every prisoner other than the counter has flipped switch A at    *)
  (* least once--and hence has been in the room at least once.  Since the  *)
  (* counter increments the count only when in the room, and Done implies  *)
  (* count > 0, it also implies that the counter has been in the room.     *)
  (*************************************************************************)
  [](Done => (\A i \in Prisoner \ {Counter} : timesSwitched[i] > 0))

Liveness == <>Done
  (*************************************************************************)
  (* This asserts that Done is eventually true, so the prisoners are       *)
  (* eventually released.                                                  *)
  (*************************************************************************)
  
THEOREM Spec => Safety /\ Liveness
  (*************************************************************************)
  (* This theorem asserts that the specification satisfies properties      *)
  (* Safety and Liveness.  TLC verifies this in a few seconds for the case *)
  (* of a half dozen prisoners.  It also quickly provides a counterexample *)
  (* if Done is changed to assert a smaller value of count.                *)
  (*************************************************************************)

CountInvariant ==
  (*************************************************************************)
  (* This is an invariant of Spec.  From its invariance, one can easily    *)
  (* prove that Spec satisfies its safety property.                        *)
  (*************************************************************************)
  LET totalSwitched ==
        (*******************************************************************)
        (* A recursive definition of the sum, over all p in OtherPrisoner, *)
        (* of timesSwitched[p].                                            *)
        (*******************************************************************)
        LET sum[S \in SUBSET OtherPrisoner] ==
              IF S = {} THEN 0
                        ELSE LET p == CHOOSE pr \in S : TRUE
                             IN  timesSwitched[p] + sum[S \ {p}]
        IN  sum[OtherPrisoner]
      oneIfUp == IF switchAUp THEN 1 ELSE 0
        (*******************************************************************)
        (* Equals 1 if switch A is up, 0 otherwise.                        *)
        (*******************************************************************)
  IN  count \in {totalSwitched - oneIfUp, totalSwitched - oneIfUp + 1}
=============================================================================
