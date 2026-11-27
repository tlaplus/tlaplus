------------------------------ MODULE Github1524 -----------------------------
\* Reproducer for https://github.com/tlaplus/tlaplus/issues/1524
\* A renamed label reached by `call P(); goto L` is not updated in the call
\* frame, so the caller never resumes at the renamed label.

EXTENDS Sequences

(* --algorithm CallGotoLabelCollision {
variables x = FALSE;

procedure NoOp() {
Body:
    return;
}

process (First = 1) {
Start:
    call NoOp();
    goto Shared;
Shared:
    x := TRUE;
}

process (Second = 2) {
Shared:
    goto Shared;
}
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "7cdf3506" /\ chksum(tla) = "9341dffa")
\* Label Shared of process First at line 21 col 5 changed to Shared_
VARIABLES pc, x, stack

vars == << pc, x, stack >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ x = FALSE
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "Start"
                                        [] self = 2 -> "Shared"]

Body(self) == /\ pc[self] = "Body"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ x' = x

NoOp(self) == Body(self)

Start == /\ pc[1] = "Start"
         /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "NoOp",
                                               pc        |->  "Shared_" ] >>
                                           \o stack[1]]
         /\ pc' = [pc EXCEPT ![1] = "Body"]
         /\ x' = x

Shared_ == /\ pc[1] = "Shared_"
           /\ x' = TRUE
           /\ pc' = [pc EXCEPT ![1] = "Done"]
           /\ stack' = stack

First == Start \/ Shared_

Shared == /\ pc[2] = "Shared"
          /\ pc' = [pc EXCEPT ![2] = "Shared"]
          /\ UNCHANGED << x, stack >>

Second == Shared

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == First \/ Second
           \/ (\E self \in ProcSet: NoOp(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Inv == x = FALSE
=============================================================================
