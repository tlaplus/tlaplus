---------------------------- MODULE Factorial2 --------------------------- 
EXTENDS Naturals, Sequences, TLC

(***************************************************************************
Factorial Algorithm with 2 procedures

--algorithm Factorial
  variable result = 1;        
  procedure FactProc(arg1 = 0 )    
    variable u = 1 ;
    begin p1 : if arg1 = 0
                 then return;     
                 else result := result * arg1;
                      call FactProc2 ( arg1 - 1 ) ;
                      b: return;
               end if;
    end procedure
  procedure FactProc2(arg2 = 0)    
    variable u2 = 1 ;
    begin p12 : if arg2 = 0
                 then return;     
                 else result := result * arg2;
                      call FactProc ( arg2 - 1 ) ;
                      return;
               end if;
    end procedure
  begin
    a1 : call FactProc( 5 ) ;
    a2 : if result = 120  then print <<"Correct =", 120>>;
                          else print <<"Error = ", result>> ;
         end if;
  end algorithm
***************************************************************************)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-7a6949afa2a72d41ea8a9ba97e423c98
VARIABLES result, pc, stack, arg1, u, arg2, u2

vars == << result, pc, stack, arg1, u, arg2, u2 >>

Init == (* Global variables *)
        /\ result = 1
        (* Procedure FactProc *)
        /\ arg1 = 0
        /\ u = 1
        (* Procedure FactProc2 *)
        /\ arg2 = 0
        /\ u2 = 1
        /\ stack = << >>
        /\ pc = "a1"

p1 == /\ pc = "p1"
      /\ IF arg1 = 0
            THEN /\ pc' = Head(stack).pc
                 /\ u' = Head(stack).u
                 /\ arg1' = Head(stack).arg1
                 /\ stack' = Tail(stack)
                 /\ UNCHANGED << result, arg2, u2 >>
            ELSE /\ result' = result * arg1
                 /\ /\ arg2' = arg1 - 1
                    /\ stack' = << [ procedure |->  "FactProc2",
                                     pc        |->  "b",
                                     u2        |->  u2,
                                     arg2      |->  arg2 ] >>
                                 \o stack
                 /\ u2' = 1
                 /\ pc' = "p12"
                 /\ UNCHANGED << arg1, u >>

b == /\ pc = "b"
     /\ pc' = Head(stack).pc
     /\ u' = Head(stack).u
     /\ arg1' = Head(stack).arg1
     /\ stack' = Tail(stack)
     /\ UNCHANGED << result, arg2, u2 >>

FactProc == p1 \/ b

p12 == /\ pc = "p12"
       /\ IF arg2 = 0
             THEN /\ pc' = Head(stack).pc
                  /\ u2' = Head(stack).u2
                  /\ arg2' = Head(stack).arg2
                  /\ stack' = Tail(stack)
                  /\ UNCHANGED << result, arg1, u >>
             ELSE /\ result' = result * arg2
                  /\ /\ arg1' = arg2 - 1
                     /\ stack' = << [ procedure |->  "FactProc",
                                      pc        |->  Head(stack).pc,
                                      u         |->  u,
                                      arg1      |->  arg1 ] >>
                                  \o Tail(stack)
                     /\ u2' = Head(stack).u2
                  /\ u' = 1
                  /\ pc' = "p1"
                  /\ arg2' = arg2

FactProc2 == p12

a1 == /\ pc = "a1"
      /\ /\ arg1' = 5
         /\ stack' = << [ procedure |->  "FactProc",
                          pc        |->  "a2",
                          u         |->  u,
                          arg1      |->  arg1 ] >>
                      \o stack
      /\ u' = 1
      /\ pc' = "p1"
      /\ UNCHANGED << result, arg2, u2 >>

a2 == /\ pc = "a2"
      /\ IF result = 120
            THEN /\ PrintT(<<"Correct =", 120>>)
            ELSE /\ PrintT(<<"Error = ", result>>)
      /\ pc' = "Done"
      /\ UNCHANGED << result, stack, arg1, u, arg2, u2 >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == FactProc \/ FactProc2 \/ a1 \/ a2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-6c949f27864a3ffc1d874b0a64419ab7


Invariant == result \in Nat
=============================================================================
