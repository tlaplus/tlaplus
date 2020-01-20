----------------------------- MODULE MPFactorial2 ---------------------------- 
EXTENDS Naturals, Sequences, TLC

(***************************************************************************
Factorial Algorithm with 2 procedures

--algorithm Factorial
  variable result = [i \in 1..3 |-> 1];        
  procedure FactProc(arg1 = 0 )    
    variable u = 1 ;
    begin p1 : if arg1 = 0
                 then return;     
                 else result[self] := result[self] * arg1;
                      call FactProc2 ( arg1 - 1 ) ;
                      b: return;
               end if;
    end procedure
  procedure FactProc2(arg2 = 0)    
    variable u2 = 1 ;
    begin p12 : if arg2 = 0
                 then return;     
                 else result[self] := result[self] * arg2;
                      call FactProc ( arg2 - 1 ) ;
                      return;
               end if;
    end procedure
  process Main \in 1..2
  begin
    a1 : call FactProc( 5 ) ;
    a2 : assert result[self] = 120  
  end process
  process Minor = 3
  begin
    b1 : call FactProc( 5 ) ;
    b2 : assert result[3] = 120 
  end process
  end algorithm
***************************************************************************)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b4a39db84a865a6dcb14d3b14f4d88b3
VARIABLES result, pc, stack, arg1, u, arg2, u2

vars == << result, pc, stack, arg1, u, arg2, u2 >>

ProcSet == (1..2) \cup {3}

Init == (* Global variables *)
        /\ result = [i \in 1..3 |-> 1]
        (* Procedure FactProc *)
        /\ arg1 = [ self \in ProcSet |-> 0]
        /\ u = [ self \in ProcSet |-> 1]
        (* Procedure FactProc2 *)
        /\ arg2 = [ self \in ProcSet |-> 0]
        /\ u2 = [ self \in ProcSet |-> 1]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..2 -> "a1"
                                        [] self = 3 -> "b1"]

p1(self) == /\ pc[self] = "p1"
            /\ IF arg1[self] = 0
                  THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ u' = [u EXCEPT ![self] = Head(stack[self]).u]
                       /\ arg1' = [arg1 EXCEPT ![self] = Head(stack[self]).arg1]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << result, arg2, u2 >>
                  ELSE /\ result' = [result EXCEPT ![self] = result[self] * arg1[self]]
                       /\ /\ arg2' = [arg2 EXCEPT ![self] = arg1[self] - 1]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FactProc2",
                                                                   pc        |->  "b",
                                                                   u2        |->  u2[self],
                                                                   arg2      |->  arg2[self] ] >>
                                                               \o stack[self]]
                       /\ u2' = [u2 EXCEPT ![self] = 1]
                       /\ pc' = [pc EXCEPT ![self] = "p12"]
                       /\ UNCHANGED << arg1, u >>

b(self) == /\ pc[self] = "b"
           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
           /\ u' = [u EXCEPT ![self] = Head(stack[self]).u]
           /\ arg1' = [arg1 EXCEPT ![self] = Head(stack[self]).arg1]
           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
           /\ UNCHANGED << result, arg2, u2 >>

FactProc(self) == p1(self) \/ b(self)

p12(self) == /\ pc[self] = "p12"
             /\ IF arg2[self] = 0
                   THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ u2' = [u2 EXCEPT ![self] = Head(stack[self]).u2]
                        /\ arg2' = [arg2 EXCEPT ![self] = Head(stack[self]).arg2]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << result, arg1, u >>
                   ELSE /\ result' = [result EXCEPT ![self] = result[self] * arg2[self]]
                        /\ /\ arg1' = [arg1 EXCEPT ![self] = arg2[self] - 1]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FactProc",
                                                                    pc        |->  Head(stack[self]).pc,
                                                                    u         |->  u[self],
                                                                    arg1      |->  arg1[self] ] >>
                                                                \o Tail(stack[self])]
                           /\ u2' = [u2 EXCEPT ![self] = Head(stack[self]).u2]
                        /\ u' = [u EXCEPT ![self] = 1]
                        /\ pc' = [pc EXCEPT ![self] = "p1"]
                        /\ arg2' = arg2

FactProc2(self) == p12(self)

a1(self) == /\ pc[self] = "a1"
            /\ /\ arg1' = [arg1 EXCEPT ![self] = 5]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FactProc",
                                                        pc        |->  "a2",
                                                        u         |->  u[self],
                                                        arg1      |->  arg1[self] ] >>
                                                    \o stack[self]]
            /\ u' = [u EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << result, arg2, u2 >>

a2(self) == /\ pc[self] = "a2"
            /\ Assert(result[self] = 120, 
                      "Failure of assertion at line 30, column 10.")
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << result, stack, arg1, u, arg2, u2 >>

Main(self) == a1(self) \/ a2(self)

b1 == /\ pc[3] = "b1"
      /\ /\ arg1' = [arg1 EXCEPT ![3] = 5]
         /\ stack' = [stack EXCEPT ![3] = << [ procedure |->  "FactProc",
                                               pc        |->  "b2",
                                               u         |->  u[3],
                                               arg1      |->  arg1[3] ] >>
                                           \o stack[3]]
      /\ u' = [u EXCEPT ![3] = 1]
      /\ pc' = [pc EXCEPT ![3] = "p1"]
      /\ UNCHANGED << result, arg2, u2 >>

b2 == /\ pc[3] = "b2"
      /\ Assert(result[3] = 120, 
                "Failure of assertion at line 35, column 10.")
      /\ pc' = [pc EXCEPT ![3] = "Done"]
      /\ UNCHANGED << result, stack, arg1, u, arg2, u2 >>

Minor == b1 \/ b2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Minor
           \/ (\E self \in ProcSet: FactProc(self) \/ FactProc2(self))
           \/ (\E self \in 1..2: Main(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..2 : WF_vars(Main(self)) /\ WF_vars(FactProc(self)) /\ WF_vars(FactProc2(self))
        /\ WF_vars(Minor) /\ WF_vars(FactProc(3)) /\ WF_vars(FactProc2(3))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-81af4b8b8e1c44a573ab6b21fa7843b0


Invariant == result \in Nat
=============================================================================
