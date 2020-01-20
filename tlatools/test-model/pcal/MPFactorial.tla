----------------------------- MODULE MPFactorial ----------------------------- 
EXTENDS Naturals, Sequences, TLC

(***************************************************************************
--algorithm Factorial
  variable result = [i \in 1..3 |-> 1];        \* are comments ok?
  procedure FactProc(arg1 (* = 0 *) )    (* are comments ok? *)
   (* what about (* nested multi-line *)
       comments? *)
    variable u = 1 ;
    begin p1 : if arg1 = 0
                 then return;     \* HERE IS A 
                 else result[self] := result[self] * arg1;
                      call FactProc ( arg1 - 1) ;
                      return;
               end if;
    end procedure
  process Main \in 1..2 
    begin
    a1 : call FactProc( 5 ) ;
    a2 : assert result[self] = 120 ;
  end process
  process Minor = 3
    begin
    b1 : call FactProc( 5 ) ;
    b2 : assert result[3] = 120 ;
  end process
  end algorithm
***************************************************************************)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-1dbfa1687c2aacb174fffdcfcb1e6b08
CONSTANT defaultInitValue
VARIABLES result, pc, stack, arg1, u

vars == << result, pc, stack, arg1, u >>

ProcSet == (1..2) \cup {3}

Init == (* Global variables *)
        /\ result = [i \in 1..3 |-> 1]
        (* Procedure FactProc *)
        /\ arg1 = [ self \in ProcSet |-> defaultInitValue]
        /\ u = [ self \in ProcSet |-> 1]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..2 -> "a1"
                                        [] self = 3 -> "b1"]

p1(self) == /\ pc[self] = "p1"
            /\ IF arg1[self] = 0
                  THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ u' = [u EXCEPT ![self] = Head(stack[self]).u]
                       /\ arg1' = [arg1 EXCEPT ![self] = Head(stack[self]).arg1]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED result
                  ELSE /\ result' = [result EXCEPT ![self] = result[self] * arg1[self]]
                       /\ arg1' = [arg1 EXCEPT ![self] = arg1[self] - 1]
                       /\ u' = [u EXCEPT ![self] = 1]
                       /\ pc' = [pc EXCEPT ![self] = "p1"]
                       /\ stack' = stack

FactProc(self) == p1(self)

a1(self) == /\ pc[self] = "a1"
            /\ /\ arg1' = [arg1 EXCEPT ![self] = 5]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FactProc",
                                                        pc        |->  "a2",
                                                        u         |->  u[self],
                                                        arg1      |->  arg1[self] ] >>
                                                    \o stack[self]]
            /\ u' = [u EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED result

a2(self) == /\ pc[self] = "a2"
            /\ Assert(result[self] = 120, 
                      "Failure of assertion at line 21, column 10.")
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << result, stack, arg1, u >>

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
      /\ UNCHANGED result

b2 == /\ pc[3] = "b2"
      /\ Assert(result[3] = 120, 
                "Failure of assertion at line 26, column 10.")
      /\ pc' = [pc EXCEPT ![3] = "Done"]
      /\ UNCHANGED << result, stack, arg1, u >>

Minor == b1 \/ b2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Minor
           \/ (\E self \in ProcSet: FactProc(self))
           \/ (\E self \in 1..2: Main(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..2 : WF_vars(Main(self)) /\ WF_vars(FactProc(self))
        /\ WF_vars(Minor) /\ WF_vars(FactProc(3))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c530d8d4ac433df112955db00ba9f4a7


Invariant == result \in Nat
=============================================================================
