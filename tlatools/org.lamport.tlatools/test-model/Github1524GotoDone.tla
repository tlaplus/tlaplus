------------------------ MODULE Github1524GotoDone -------------------------
EXTENDS Sequences
\* Done is the implicit termination label and is not in the symbol table.
\* call NoOp(); goto Done must translate and then stop.
(* --algorithm GotoDone {
procedure NoOp() {
  Body:
    return;
}
{
  Start:
    call NoOp();
    goto Done;
}
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "e045062d" /\ chksum(tla) = "1c3bc4c7")
VARIABLES pc, stack

vars == << pc, stack >>

Init == /\ stack = << >>
        /\ pc = "Start"

Body == /\ pc = "Body"
        /\ pc' = Head(stack).pc
        /\ stack' = Tail(stack)

NoOp == Body

Start == /\ pc = "Start"
         /\ stack' = << [ procedure |->  "NoOp",
                          pc        |->  "Done" ] >>
                      \o stack
         /\ pc' = "Body"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == NoOp \/ Start
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
Inv == pc # "Done"
====
