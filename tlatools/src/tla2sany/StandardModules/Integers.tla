-------------------------------- MODULE Integers ----------------------------
(***************************************************************************)
(* A dummy module that declares the operators that are defined in the      *)
(* real Integers module.                                                   *)
(***************************************************************************)
EXTENDS Naturals

Int  ==  { } \* tlc2.module.Integers.Int()
-. a == 0 - a \* tlc2.module.Integers.Neg(IntValue)
=============================================================================
