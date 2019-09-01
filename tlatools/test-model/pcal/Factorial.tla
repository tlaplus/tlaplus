------------------------------ MODULE Factorial ----------------------------- 
EXTENDS Naturals, Sequences, TLC

(***************************************************************************
--algorithm Factorial
  variable result = 1;        \* are comments ok?
  procedure FactProc(arg1 = 0)    (* are comments ok? *)
   (* what about (* nested multi-line *)
       comments? *)
    variable u = 1 ;
    begin p1 : if arg1 = 0
                 then return;     \* HERE IS A 
                 else result := result * arg1;
                      call FactProc ( arg1 - 1 ) ;
                      return;
               end if;
    end procedure
  begin
    a1 : call FactProc( 5 ) ;
    a2 : assert result = 120 ;
  end algorithm
***************************************************************************)

\* BEGIN TRANSLATION PC-02a2ac74d9c38708d7090e69a785c03474acff0645e945258a372a5581beb94a
VARIABLES result, pc, stack, arg1, u

vars == << result, pc, stack, arg1, u >>

Init == (* Global variables *)
        /\ result = 1
        (* Procedure FactProc *)
        /\ arg1 = 0
        /\ u = 1
        /\ stack = << >>
        /\ pc = "a1"

p1 == /\ pc = "p1"
      /\ IF arg1 = 0
            THEN /\ pc' = Head(stack).pc
                 /\ u' = Head(stack).u
                 /\ arg1' = Head(stack).arg1
                 /\ stack' = Tail(stack)
                 /\ UNCHANGED result
            ELSE /\ result' = result * arg1
                 /\ arg1' = arg1 - 1
                 /\ u' = 1
                 /\ pc' = "p1"
                 /\ stack' = stack

FactProc == p1

a1 == /\ pc = "a1"
      /\ /\ arg1' = 5
         /\ stack' = << [ procedure |->  "FactProc",
                          pc        |->  "a2",
                          u         |->  u,
                          arg1      |->  arg1 ] >>
                      \o stack
      /\ u' = 1
      /\ pc' = "p1"
      /\ UNCHANGED result

a2 == /\ pc = "a2"
      /\ Assert(result = 120, "Failure of assertion at line 20, column 10.")
      /\ pc' = "Done"
      /\ UNCHANGED << result, stack, arg1, u >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == FactProc \/ a1 \/ a2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION TPC-7c805838962eadbc72b85d7222677303ac50633afe1c26e6523d907573e755f7


Invariant == result \in Nat
=============================================================================
