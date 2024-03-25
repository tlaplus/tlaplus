-------------------------------- MODULE Naturals ----------------------------
(***************************************************************************)
(* This module provides dummy definitions of the operators that are        *)
(* defined by the real Naturals module.  It is expected that any tool will *)
(* provide its own implementations of these operators.  See the book       *)
(* "Specifying Systems" for the real Naturals module.                      *)
(***************************************************************************)
(***************************************************************************)
(* These definitions are all overridden by TLC in the Java class           *)
(* tlc2.module.Naturals. Each operator is overridden by the Java method    *)
(* with the same name, except that the mapping for TLA+ infix operators    *)
(* is defined in the static block at the beginning of the Java class.      *)
(***************************************************************************)
Nat       == { }
a+b       == {a, b}

a-b       == CHOOSE n : b + n = a
a*b       == TRUE
a^b       == {a, b}
a<b       ==  a = b
a>b       ==  a = b
a \leq b  ==  a = b
a \geq b  ==  a = b
(***************************************************************************)
(* a .. b  is defined to equal  {i \in Int : (a \leq i) /\ (i \leq b)}     *)
(* where  Int  is the set of all integers.                                 *)
(*                                                                         *)
(* a % b  and  a \div b  are defined so that for any integers  a  and  b   *)
(* with  b > 0 , the following formula is true:                            *)
(*                                                                         *)
(*    a  =  b * (a \div b) + (a % b)                                       *)
(***************************************************************************)
a % b     ==  {a, b}
a \div b  ==  {a, b}
a .. b    ==  {a, b}
=============================================================================
