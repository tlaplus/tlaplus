-------------------------- MODULE Randomization------------------------------
(***************************************************************************)
(* This module defines operators for choosing pseudo-random subsets of a   *)
(* set.  It is useful for inductive invariance checking, where the         *)
(* operators appear only in the initial predicate.  However, it may have   *)
(* other uses.                                                             *)
(*                                                                         *)
(* In breadth-first search model checking, the pseudo-random choices made  *)
(* when computing possible steps satisfying the next-state relation are    *)
(* determined by the first state of the step.  Thus, the choices made for  *)
(* a particular state will be the same in successive runs of TLC.  This is *)
(* done to permit TLC to generate an error trace if an error is found.     *)
(* This applies only when TLC is run in breadth-first search mode.  In     *)
(* particular, the choices made in simulation mode are independent of the  *)
(* state for which they are made.                                          *)
(***************************************************************************)

(***************************************************************************)
(* Except for TestRandomSetOfSubsets, all these definitions are overridden *)
(* by TLC in the Java class tlc2.module.Randomization.  Each operator is   *)
(* overridden by the Java method with the same name.                       *)
(***************************************************************************)
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

(***************************************************************************)
(* RandomSubset(k, S) equals a randomly chosen subset of S containing k    *)
(* elements, where 0 < k < Cardinality(S).                                 *)
(***************************************************************************)
RandomSubset(k, S) == CHOOSE T \in SUBSET S : Cardinality(T) = T

(***************************************************************************)
(* RandomSetOfSubsets(k, n, S) equals a pseudo-randomly chosen set of      *)
(* subsets of S -- that is, a randomly chosen subset of SUBSET S .  Thus,  *)
(* each element T of this set is a subset of S.  Each such T is chosen so  *)
(* that each element of S has a probability n / Cardinality(S) of being in *)
(* T.  Thus, the average number of elements in each chosen subset T is n.  *)
(* The set RandomSetOfSubsets(k, n, S) is obtained by making k such        *)
(* choices of T .  Because this can produce duplicate choices, the number  *)
(* of elements T in this set may be less than k.  The average number of    *)
(* elements in RandomSetOfSubsets(k, n, S) seems to be difficult to        *)
(* compute in general.  However, there is very little variation in the     *)
(* actual number of elements in the chosen set for fixed values of k, n,   *)
(* and Cardinality(S).  You can therefore use the operator                 *)
(* TestRandomSetOfSubsets defined below to find out approximately how      *)
(* close to k the cardinality of the chosen set of subsets is.             *)
(***************************************************************************)
RandomSetOfSubsets(k, n, S) == CHOOSE T \in SUBSET SUBSET S :
											  Cardinality(T) \leq k

(***************************************************************************)
(* The value of TestRandomSetOfSubsets(k, n, S) is a sequence of five      *)
(* values that are the cardinality of the set of subsets produced by five  *)
(* executions of RandomSetOfSubsets(k, n, S).  For constant values of k,   *)
(* n, and S, you can enter TestRandomSetOfSubsets(k, n, S) in the Evaluate *)
(* Constant Expression section of a TLC model in the TLA+ Toolbox.         *)
(* Running TLC will then tell you the approximate number of elements in    *)
(* the set of subsets produced by RandomSetOfSubsets for these parameters. *)
(* You can then choose k to obtain a set of the desired size.              *)
(***************************************************************************)
TestRandomSetOfSubsets(k, n, S) ==
              [i \in 1..5 |-> Cardinality(RandomSetOfSubsets(k, n, S))]

=============================================================================
