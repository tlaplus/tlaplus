------------------------------- MODULE Either4 ------------------------------ 
EXTENDS Naturals, Sequences, TLC

(* --algorithm Either
      process Foo \in {1, 2}
      variables x = 0 ; y = 0 ; z = 0 ;
      begin a: either    x := 1 ; 
                      b: x := x + 1; 
                   or y := 1 ; c: y := y + 1;
                   or z := 100
               end either ;
            d: either when x = 0 ; z := z + 1 ;
                   or when x = 2 ; z := z + 3 ;
               end either ;     
               assert (x+y = 2) \/ ((z = 101) /\ (x+y=0));
               assert (z < 100) => (z = x + 1) ;
     end process
     end algorithm
*)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9a6afbc4f2a88a20f8db8f24ec88b676
VARIABLES pc, x, y, z

vars == << pc, x, y, z >>

ProcSet == ({1, 2})

Init == (* Process Foo *)
        /\ x = [self \in {1, 2} |-> 0]
        /\ y = [self \in {1, 2} |-> 0]
        /\ z = [self \in {1, 2} |-> 0]
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ \/ /\ x' = [x EXCEPT ![self] = 1]
                 /\ pc' = [pc EXCEPT ![self] = "b"]
                 /\ UNCHANGED <<y, z>>
              \/ /\ y' = [y EXCEPT ![self] = 1]
                 /\ pc' = [pc EXCEPT ![self] = "c"]
                 /\ UNCHANGED <<x, z>>
              \/ /\ z' = [z EXCEPT ![self] = 100]
                 /\ pc' = [pc EXCEPT ![self] = "d"]
                 /\ UNCHANGED <<x, y>>

b(self) == /\ pc[self] = "b"
           /\ x' = [x EXCEPT ![self] = x[self] + 1]
           /\ pc' = [pc EXCEPT ![self] = "d"]
           /\ UNCHANGED << y, z >>

c(self) == /\ pc[self] = "c"
           /\ y' = [y EXCEPT ![self] = y[self] + 1]
           /\ pc' = [pc EXCEPT ![self] = "d"]
           /\ UNCHANGED << x, z >>

d(self) == /\ pc[self] = "d"
           /\ \/ /\ x[self] = 0
                 /\ z' = [z EXCEPT ![self] = z[self] + 1]
              \/ /\ x[self] = 2
                 /\ z' = [z EXCEPT ![self] = z[self] + 3]
           /\ Assert((x[self]+y[self] = 2) \/ ((z'[self] = 101) /\ (x[self]+y[self]=0)), 
                     "Failure of assertion at line 15, column 16.")
           /\ Assert((z'[self] < 100) => (z'[self] = x[self] + 1), 
                     "Failure of assertion at line 16, column 16.")
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << x, y >>

Foo(self) == a(self) \/ b(self) \/ c(self) \/ d(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {1, 2}: Foo(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {1, 2} : WF_vars(Foo(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-8050fab129ad8ea32f6a8eefb5f96b57

=============================================================================
