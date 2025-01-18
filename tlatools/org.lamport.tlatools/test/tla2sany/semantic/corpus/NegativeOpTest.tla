-------------------------- MODULE NegativeOpTest ----------------------------
EXTENDS Semantics

(* ID: op *)
op((* ID: op!-. *) -._) == RefersTo(-1, "op!-.")

CONSTANT (* ID: constant_negative *) -._
ASSUME RefersTo(-1, "constant_negative")

(* ID: -. *)
-. x == x
ASSUME RefersTo(-1, "-.")

=============================================================================
