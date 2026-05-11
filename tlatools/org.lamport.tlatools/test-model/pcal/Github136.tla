------------------------------ MODULE Github136 -----------------------------
\* Regression test for https://github.com/tlaplus/tlaplus/issues/136
\* The PlusCal translator used to choke on a top-level comma inside an
\* INSTANCE ... WITH clause appearing within a `define' block.

EXTENDS Naturals

(*--algorithm Github136
variables x = 0;
define
    Inner == INSTANCE Github136Inner WITH Foo1 <- 3, Foo2 <- 4
end define;
begin
    Step: x := Inner!Sum;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "a38a0cc5" /\ chksum(tla) = "81c563ad")
VARIABLES pc, x

(* define statement *)
Inner == INSTANCE Github136Inner WITH Foo1 <- 3, Foo2 <- 4


vars == << pc, x >>

Init == (* Global variables *)
        /\ x = 0
        /\ pc = "Step"

Step == /\ pc = "Step"
        /\ x' = Inner!Sum
        /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Step
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

XCorrect == x \in {0, 7}
=============================================================================
