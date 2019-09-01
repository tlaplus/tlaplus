
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
					
\* BEGIN TRANSLATION PC-1b44ee1584c71e267451734f7bfed1f6641f31930b435e06c1983f1e780256b6
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

\* END TRANSLATION TPC-0a2effa1aa37e466cbdd62252c47591602b03ea80da7a10a4d8ed69f870624b1
=============================================================================
