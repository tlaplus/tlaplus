---------------------------- MODULE PrintValues ---------------------------- 

(***************************************************************************)
(* This module illustrates how to use TLC to calculate and print the       *)
(* values of TLA+ expressions.  It uses the fact that TLC checks           *)
(* assumptions.  (See the SimpleMath module in the SimpleMath folder for   *)
(* other examples of using TLC's checking of assumptions.)                 *)
(*                                                                         *)
(* We make use of operator Print defined in the standard module TLC. The   *)
(* TLA+ definition of Print is simply                                      *)
(*                                                                         *)
(*    Print(out, val) == val                                               *)
(*                                                                         *)
(* so the value of Print(e1, e2) is just the expression e2.  However,      *)
(* evaluating the expression Print(e1, e2) causes TLC to print the values  *)
(* of e1 and e2.  Thus, the statement                                      *)
(*                                                                         *)
(*    ASSUME Print(exp, TRUE)                                              *)
(*                                                                         *)
(* is a true assumption, that causes TLC to print the value of exp when    *)
(* it checks the assumption.                                               *)
(***************************************************************************)

EXTENDS Naturals, TLC
  (*************************************************************************)
  (* This statement imports into the current module the definitions of     *)
  (* arithmetic operators from the module Naturals and the definitions     *)
  (* from TLC, including that of Print.                                    *)
  (*************************************************************************)
  

(***************************************************************************)
(* Instead of having to type Print(exp, TRUE), we could just define        *)
(* PrintVal(exp) to equal Print(exp, TRUE).  However, when having TLC      *)
(* print several values, it's convenient to print a string that identifies *)
(* the value being printed.  So, we define PrintVal(id, exp) so it prints  *)
(* the pair <<id, exp>>.                                                   *)
(***************************************************************************)
PrintVal(id, exp)  ==  Print(<<id, exp>>, TRUE)


(***************************************************************************)
(* We now use an ASSUME to print some values.  The order in which TLC      *)
(* evaluates ASSUMEs is not specified.  However, TLC evaluates the clauses *)
(* of a conjunction in order.  So, we use a single ASSUME to the get       *)
(* values printed in the desired order.                                    *)
(***************************************************************************)
ASSUME
  /\ PrintVal("Three more cats: ",
              [cat |-> 1, dog |-> "d"].cat + 3)
  /\ PrintVal("Here's a record: ",
              [ [game |-> "baseball", player |-> "Marris", homers |-> 61]
                   EXCEPT !.player = "McGuire",
                          !.homers = @+9 ] )
=============================================================================