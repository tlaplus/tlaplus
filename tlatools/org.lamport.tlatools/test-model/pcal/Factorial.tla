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

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-8354903ee5c9ddae0b8bb4f55d782009
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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-53ca468546a563a45762642894b2b2a3


Invariant == result \in Nat
=============================================================================
