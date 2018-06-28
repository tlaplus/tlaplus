-------------------------------- MODULE Integers ----------------------------
(***************************************************************************)
(* This module provides dummy definitions of the operators that are        *)
(* defined by the real Integers module.  It is expected that any tool will *)
(* provide its own implementations of these operators.  See the book       *)
(* "Specifying Systems" for the real Integers module.                      *)
(***************************************************************************)
(***************************************************************************)
(* The two definitions here and the definitions imported from the Naturals *)
(* module are overridden by TLC in the Java class tlc2.module.Integers.    *)
(* Each operator is overridden by the Java method with the same name,      *)
(* except that the mappings for the prefix - operator and the TLA+ infix   *)
(* operators are defined in the static block at the beginning of the Java  *)
(* class.                                                                  *)
(***************************************************************************)
EXTENDS Naturals

Int  ==  { }
(***************************************************************************)
(* This defines the prefix - operator.                                     *)
(***************************************************************************)
-. a == 0 - a
=============================================================================
