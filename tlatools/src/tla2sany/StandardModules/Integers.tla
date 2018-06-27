-------------------------------- MODULE Integers ----------------------------
(***************************************************************************)
(* This module provides dummy definitions of the operators that are        *)
(* defined by the real Integers module.  It is expected that any tool will *)
(* provide its own implementations of these operators.  See the book       *)
(* "Specifying Systems" for the real Integers module.                      *)
(***************************************************************************)
EXTENDS Naturals

Int  ==  { } \* tlc2.module.Integers.Int()
(***************************************************************************)
(* This defines the prefix - operator.                                     *)
(***************************************************************************)
-. a == 0 - a \* tlc2.module.Integers.Neg(IntValue)
=============================================================================
