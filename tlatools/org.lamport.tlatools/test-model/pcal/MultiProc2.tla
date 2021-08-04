----------------------------- MODULE MultiProc2 ---------------------------- 
EXTENDS Sequences, Naturals, TLC

(*   

  --algorithm MultiProc2
    variables
      x = [i \in ProcSet |-> CASE i = 41 -> 1 []
                                 i = 42 -> 2 []
                                 i = 43 -> 3];
      sum = 0 ;
      done = {};
    procedure Sum(arg = 0)
      variable u = 1 ;
      begin p1 : u := u + arg ;
            p2 : sum := sum + u;
                 return;
      end procedure
    process ProcA = 41
      variable y = 0  ;
      begin a1 : call Sum( x [ 41 ] + y ) ;
            a2 : done := done \cup { 41 } ;
            a3 : when done = { 41, 42, 43 } ;
                 when Print ( sum , TRUE ) ;
      end process
    process ProcB \in {42, 43}
      variable z \in {2, 3} ;
      begin b1 : call Sum ( x [ self ] + z ) ;
            b2 : done := done \cup { self } ;
      end process
    end algorithm 
*)
                    
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-6a3f53faa6a08b14086cf6736a14399e
VARIABLES x, sum, done, pc, stack, arg, u, y, z

vars == << x, sum, done, pc, stack, arg, u, y, z >>

ProcSet == {41} \cup ({42, 43})

Init == (* Global variables *)
        /\ x = [i \in ProcSet |-> CASE i = 41 -> 1 []
                                      i = 42 -> 2 []
                                      i = 43 -> 3]
        /\ sum = 0
        /\ done = {}
        (* Procedure Sum *)
        /\ arg = [ self \in ProcSet |-> 0]
        /\ u = [ self \in ProcSet |-> 1]
        (* Process ProcA *)
        /\ y = 0
        (* Process ProcB *)
        /\ z \in [{42, 43} -> {2, 3}]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = 41 -> "a1"
                                        [] self \in {42, 43} -> "b1"]

p1(self) == /\ pc[self] = "p1"
            /\ u' = [u EXCEPT ![self] = u[self] + arg[self]]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << x, sum, done, stack, arg, y, z >>

p2(self) == /\ pc[self] = "p2"
            /\ sum' = sum + u[self]
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ u' = [u EXCEPT ![self] = Head(stack[self]).u]
            /\ arg' = [arg EXCEPT ![self] = Head(stack[self]).arg]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << x, done, y, z >>

Sum(self) == p1(self) \/ p2(self)

a1 == /\ pc[41] = "a1"
      /\ /\ arg' = [arg EXCEPT ![41] = x [ 41 ] + y]
         /\ stack' = [stack EXCEPT ![41] = << [ procedure |->  "Sum",
                                                pc        |->  "a2",
                                                u         |->  u[41],
                                                arg       |->  arg[41] ] >>
                                            \o stack[41]]
      /\ u' = [u EXCEPT ![41] = 1]
      /\ pc' = [pc EXCEPT ![41] = "p1"]
      /\ UNCHANGED << x, sum, done, y, z >>

a2 == /\ pc[41] = "a2"
      /\ done' = (done \cup { 41 })
      /\ pc' = [pc EXCEPT ![41] = "a3"]
      /\ UNCHANGED << x, sum, stack, arg, u, y, z >>

a3 == /\ pc[41] = "a3"
      /\ done = { 41, 42, 43 }
      /\ Print ( sum , TRUE )
      /\ pc' = [pc EXCEPT ![41] = "Done"]
      /\ UNCHANGED << x, sum, done, stack, arg, u, y, z >>

ProcA == a1 \/ a2 \/ a3

b1(self) == /\ pc[self] = "b1"
            /\ /\ arg' = [arg EXCEPT ![self] = x [ self ] + z[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Sum",
                                                        pc        |->  "b2",
                                                        u         |->  u[self],
                                                        arg       |->  arg[self] ] >>
                                                    \o stack[self]]
            /\ u' = [u EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << x, sum, done, y, z >>

b2(self) == /\ pc[self] = "b2"
            /\ done' = (done \cup { self })
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << x, sum, stack, arg, u, y, z >>

ProcB(self) == b1(self) \/ b2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ProcA
           \/ (\E self \in ProcSet: Sum(self))
           \/ (\E self \in {42, 43}: ProcB(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ProcA) /\ WF_vars(Sum(41))
        /\ \A self \in {42, 43} : WF_vars(ProcB(self)) /\ WF_vars(Sum(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3f17bd1aee44cca22b14ef7de16f1390
=============================================================================
