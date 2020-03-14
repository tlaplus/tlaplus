----------------------------- MODULE Simple --------------------------
EXTENDS Integers

CONSTANT N
ASSUME NAssump ==  (N \in Nat) /\ (N > 0)

ExpTaut(S) == \A ss \in SUBSET S: ss = {} \/ \A e \in ss: e \in S

(****************************************************************************
--algorithm Simple {
    variables x = [i \in 0..N-1 |-> 0],
              y = [i \in 0..N-1 |-> 0],
              z \in 1..3;

    process (proc \in 0..N-1) {
      a: x[self] := 1 ;
      b: y[self] := x[(self-1) % N]
    }
}
****************************************************************************)
\* BEGIN TRANSLATION  This is the TLA+ translation of the PlusCal code. PCal-5c58e1a73855a22c06f78d78d4dfc2a3
VARIABLES x, y, z, pc

vars == << x, y, z, pc >>

ProcSet == (0..N-1)

Init == (* Global variables *)
        /\ y = [i \in 0..N-1 |-> 0]
        /\ x = [i \in 0..N-1 |-> 0]
        /\ z \in 1..3
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ x' = [x EXCEPT ![self] = 1]
           /\ pc' = [pc EXCEPT ![self] = "b"]
           /\ y' = y /\ z' = z
           /\ ExpTaut(1..3)

b(self) == /\ x[self] = 1 /\ y[self] = 0 \* pc[self] = "b"
           /\ y' = [y EXCEPT ![self] = x[(self-1) % N]]
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ x' = x /\ z' = z
           /\ ExpTaut(1..5)

proc(self) == a(self) \/ b(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 0..N-1: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION TLA-0e9e0633cd25a2a6c948e18f4aa9ab0c

==========================================================
