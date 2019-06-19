---- MODULE CallGotoUnlabeledTest ----

(* --algorithm CallGotoUnlabeledTest

variable x = 0;

procedure Foo()
begin
\*Q: \* Not needed anymore.
  x := x + 1;
  return;
end procedure;

begin
A:
  call Foo();
  goto C;
\*B: \* Not needed anymore.
  x := 13;
C:
  x := x - 1;
  goto A;

end algorithm *)
\* BEGIN TRANSLATION
VARIABLES x, pc, stack

vars == << x, pc, stack >>

Init == (* Global variables *)
        /\ x = 0
        /\ stack = << >>
        /\ pc = "A"

Lbl_1 == /\ pc = "Lbl_1"
         /\ x' = x + 1
         /\ pc' = Head(stack).pc
         /\ stack' = Tail(stack)

Foo == Lbl_1

A == /\ pc = "A"
     /\ stack' = << [ procedure |->  "Foo",
                      pc        |->  "C" ] >>
                  \o stack
     /\ pc' = "Lbl_1"
     /\ x' = x

Lbl_2 == /\ pc = "Lbl_2"
         /\ x' = 13
         /\ pc' = "C"
         /\ stack' = stack

C == /\ pc = "C"
     /\ x' = x - 1
     /\ pc' = "A"
     /\ stack' = stack

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Foo \/ A \/ Lbl_2 \/ C
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

====
