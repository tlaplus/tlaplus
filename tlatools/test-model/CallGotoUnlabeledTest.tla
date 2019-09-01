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
\* BEGIN TRANSLATION PC-3f2fa73e541043025def1e8d364b252055cbd346d97d1540e76635c379292a39
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

\* END TRANSLATION TPC-0007aa5acdd9b6827fba4c69957e641fc5e2c73ee8e967e91815d1b2e22a1362

====
