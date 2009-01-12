---------------------------- MODULE MCDieHarder ----------------------------- 
EXTENDS DieHarder

(***************************************************************************)
(* To have TLC find a solution, we must tell it what values to use for the *)
(* constant parameters Jug, Capacity, and Goal.  However, TLC does not     *)
(* allow one to write write function-valued expressions in a configuration *)
(* file.  So, we use this module, which extends module DieHarder, to       *)
(* define a function MCCapacity and have the configuration file TLC to     *)
(* substitute MCCapacity for Capacity.  Since we need to know the value of *)
(* Jug to define Capacity (which is a function having Jug as its domain),  *)
(* we also define MCJug and tell TLC to substitute it for Jug.             *)
(***************************************************************************)

\* The following definitions duplicate the original Die Hard problem.
MCJug == {"j1", "j2"}
MCCapacity ==
  [j \in MCJug |-> CASE j = "j1" -> 3
                     [] j = "j2" -> 5 ]
=============================================================================
