--------------------------- MODULE MultiAssignment -------------------------- 
(***************************************************************************)
(* A test of multi-assignment statements with arrays.                      *)
(***************************************************************************)

EXTENDS Naturals, TLC



(*****


--algorithm MultiAssignment
  process Proc \in 1..3
  variables A = [i \in 1..5 |-> i] ; x = 0 ;
  begin a : A[1] := A[3] ||  x := 7 || A[3] := A[1] ;
            assert <<3 , 1>> = <<A[1], A[3]>> ;
        b : assert <<3 , 1>> = <<A[1], A[3]>> ;
  end process
  end algorithm 

****)
                    
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-922bd40bbb66854d6ea0cf6dbef935cb
VARIABLES pc, A, x

vars == << pc, A, x >>

ProcSet == (1..3)

Init == (* Process Proc *)
        /\ A = [self \in 1..3 |-> [i \in 1..5 |-> i]]
        /\ x = [self \in 1..3 |-> 0]
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ /\ A' = [A EXCEPT ![self][1] = A[self][3],
                                ![self][3] = A[self][1]]
              /\ x' = [x EXCEPT ![self] = 7]
           /\ Assert(<<3 , 1>> = <<A'[self][1], A'[self][3]>>, 
                     "Failure of assertion at line 17, column 13.")
           /\ pc' = [pc EXCEPT ![self] = "b"]

b(self) == /\ pc[self] = "b"
           /\ Assert(<<3 , 1>> = <<A[self][1], A[self][3]>>, 
                     "Failure of assertion at line 18, column 13.")
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << A, x >>

Proc(self) == a(self) \/ b(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..3: Proc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..3 : WF_vars(Proc(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-6c5ff91175ea2e80dc22b1dde5479e58
=============================================================================
