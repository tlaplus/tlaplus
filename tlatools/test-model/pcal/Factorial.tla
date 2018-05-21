------------------------------ MODULE Factorial ----------------------------- 
EXTENDS Naturals, Sequences, TLC

(***************************************************************************
--algorithm Factorial
  variable result = 1;        \* are comments ok?
  procedure FactProc(arg1 = 0)    (* are comments ok? *)
   (* what about (* nested multi-line *)
       comments? *)
    variable u = 1 ;
    begin p1 : print << " recursive call ", arg1 >>;
               if arg1 = 0
                 then return;     \* HERE IS A 
                 else result := result * arg1;
                      call FactProc ( arg1 - 1 ) ;
                      return;
               end if;
    end procedure
  begin
    a1 : call FactProc( 5 ) ;
    a2 : if result = 120  then print "Correct";
                          else print "Error" ;
         end if;
         assert result = 120 ;
  end algorithm
***************************************************************************)

(************** BEGIN TRANSLATION ********************)
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
      /\ PrintT(<< " recursive call ", arg1 >>)
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
      /\ IF result = 120
            THEN /\ PrintT("Correct")
            ELSE /\ PrintT("Error")
      /\ Assert(result = 120, "Failure of assertion at line 24, column 10.")
      /\ pc' = "Done"
      /\ UNCHANGED << result, stack, arg1, u >>

Next == FactProc \/ a1 \/ a2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

(************* END TRANSLATION ********************)


Invariant == result \in Nat
=============================================================================
