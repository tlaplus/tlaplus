----------------------------- MODULE NestedMacros ---------------------------
EXTENDS Naturals, TLC

\* PlusCal options(label)
(***************************************************************************
--algorithm Test {
  variables x, y ;

  macro ff(a, b) {
    a := b
  }
  macro foo(a) {
   ff(z,a);
   y := a
  }

  macro bar(b) {
   x := b;
   foo(22)
  }
  process (foob  \in {1,2}) 
   variable z ;
  { l1 : z := 0 ; 
    l2 : bar(42);
          assert z = 22 /\ x = 42
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-45eef21f51ec0ad28fe46e4b9a7b10ce
CONSTANT defaultInitValue
VARIABLES x, y, pc, z

vars == << x, y, pc, z >>

ProcSet == ({1,2})

Init == (* Global variables *)
        /\ x = defaultInitValue
        /\ y = defaultInitValue
        (* Process foob *)
        /\ z = [self \in {1,2} |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "l1"]

l1(self) == /\ pc[self] = "l1"
            /\ z' = [z EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << x, y >>

l2(self) == /\ pc[self] = "l2"
            /\ x' = 42
            /\ z' = [z EXCEPT ![self] = 22]
            /\ y' = 22
            /\ Assert(z'[self] = 22 /\ x' = 42, 
                      "Failure of assertion at line 25, column 11.")
            /\ pc' = [pc EXCEPT ![self] = "Done"]

foob(self) == l1(self) \/ l2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {1,2}: foob(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {1,2} : WF_vars(foob(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-5f6bcf611a462be83724e9522b1f4062
=============================================================================
