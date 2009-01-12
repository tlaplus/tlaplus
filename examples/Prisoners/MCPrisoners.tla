----------------------------- MODULE MCPrisoners ----------------------------
(***************************************************************************)
(* This module checks that the invariant CountInvariant of module          *)
(* Prisoners is actually an inductive invariant of specification Spec.     *)
(* More precisely, its conjunction with TypeOK is an inductive invariant   *)
(* of the next-state action Next, meaning that it satisfies                *)
(*                                                                         *)
(*    (TypeOK /\ CountInvariant) /\  Next => (TypeOK /\ CountInvariant)'   *)
(*                                                                         *)
(* Because Init implies TypeOK, it's easy to see that this implies that    *)
(* TypeOK /\ CountInvariant is also an invariant of Spec.                  *)
(***************************************************************************)
EXTENDS Prisoners

InductiveInvariant == TypeOK /\ CountInvariant

InvTestSpec == InductiveInvariant /\ [][Next]_vars
  (*************************************************************************)
  (* InductiveInvariant is an invariant of this specification iff it is an *)
  (* inductive invariant of Next.                                          *)
  (*                                                                       *)
  (* Specification Spec is unusual because the number of states satisfying *)
  (* the type invariant is not much greater than the number of reachable   *)
  (* states, so TLC can compute all reachable states for InvTestSpec       *)
  (* almost as quickly as it can for Spec.                                 *)
  (*************************************************************************)
=============================================================================
