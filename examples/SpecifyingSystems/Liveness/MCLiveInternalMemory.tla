---------------------- MODULE MCLiveInternalMemory -------------------------
(***************************************************************************)
(* This is a module used for running TLC to check the specification LISpec *)
(* of LiveInternalMemory.  We need to tell TLC the values of the constant  *)
(* operators Send and Reply.  We define operators MCSend and MCReply and   *)
(* use the configuration file to tell TLC to substitute these operators    *)
(* for Send and Reply.  We also define MCInitMemInt, which is substituted  *)
(* for InitMemInt.                                                         *)
(*                                                                         *)
(* This module is identical to module MCInternalMemory                     *)
(* from folder CachingMemory, except it EXTENDS module LiveInternalMemory  *)
(* instead of InternalMemory.                                              *)
(***************************************************************************)

EXTENDS LiveInternalMemory

(***************************************************************************)
(* The operator Send is used in specifications in conjuncts of the form    *)
(*                                                                         *)
(* (+)  Send(p, d, memInt, memInt')                                        *)
(*                                                                         *)
(* to specify the new value of memInt.  For TLC to handle such a           *)
(* conjunct, the definition of Send must make (+) equal something of the   *)
(* form                                                                    *)
(*                                                                         *)
(*   memInt' = ...                                                         *)
(*                                                                         *)
(* (A similar observation holds for Reply.)  We define Send so that (+)    *)
(* equals                                                                  *)
(*                                                                         *)
(*   memInt' = <<p, d>>                                                    *)
(*                                                                         *)
(* If we were doing serious model checking, we might try to reduce         *)
(* the state space by letting the value of memInt remain constant,         *)
(* so we would define Send so that (+) equals                              *)
(*                                                                         *)
(*   memInt' = memInt.                                                     *)
(***************************************************************************)
MCSend(p, d, oldMemInt, newMemInt)  ==  newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) ==  newMemInt = <<p, d>>

(***************************************************************************)
(* We define MCInitMemInt, the set of initial values of memInt, to contain *)
(* the single element <<p, NoVal>>, for an arbitrary processor p.          *)
(***************************************************************************)
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}
=============================================================================

