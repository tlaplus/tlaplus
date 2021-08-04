
------------------------------- MODULE bug_05_12_31 ----------------------------- 
EXTENDS Naturals, Sequences, TLC


(*   
--algorithm Test
   procedure P(a = 7) 
      variable x = a ; y = x+1 ;
      begin P1: assert a = 1;
                assert x = a;
                assert y = a+1;
                return;
      end procedure 
     begin A: call P(1)
  end algorithm
*)
                    
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-1f8e16f0d9c2b45f0271cd3d8415f9b8
VARIABLES pc, stack, a, x, y

vars == << pc, stack, a, x, y >>

Init == (* Procedure P *)
        /\ a = 7
        /\ x = a
        /\ y = x+1
        /\ stack = << >>
        /\ pc = "A"

P1 == /\ pc = "P1"
      /\ Assert(a = 1, "Failure of assertion at line 10, column 17.")
      /\ Assert(x = a, "Failure of assertion at line 11, column 17.")
      /\ Assert(y = a+1, "Failure of assertion at line 12, column 17.")
      /\ pc' = Head(stack).pc
      /\ x' = Head(stack).x
      /\ y' = Head(stack).y
      /\ a' = Head(stack).a
      /\ stack' = Tail(stack)

P == P1

A == /\ pc = "A"
     /\ /\ a' = 1
        /\ stack' = << [ procedure |->  "P",
                         pc        |->  "Done",
                         x         |->  x,
                         y         |->  y,
                         a         |->  a ] >>
                     \o stack
     /\ x' = a'
     /\ y' = x'+1
     /\ pc' = "P1"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == P \/ A
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-6df4c643b7934c47f1761b2b8aced244
=============================================================================
