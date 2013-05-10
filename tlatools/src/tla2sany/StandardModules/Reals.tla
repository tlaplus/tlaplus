-------------------------------- MODULE Reals -------------------------------
(***************************************************************************)
(* A dummy module that declares the operators that are defined in the      *)
(* real Reals module.  It should produce an error if TLC tries to          *)
(* evaluate these operators when it shouldn't.                             *)
(***************************************************************************)
EXTENDS Integers

Real  == "Reals"
a / b == CHOOSE m \in Real : m * b = a
Infinity == CHOOSE i : (i \notin Real) /\ (\A r \in Real : i > r)
=============================================================================
