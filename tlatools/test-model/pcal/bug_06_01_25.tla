
--algorithm TestAlignment
   variable x ; y ; z = /\ \A i \in {1} : i > 0 
                        /\ \A i \in {1} : i > 0 
                        /\ \A i \in {1} : i > 0 
   define  foo == /\ \A i \in {1} : i > 0 
                  /\ \A i \in {1} : i > 0 
                  /\ \A i \in {1} : i > 0 
   end define;
   macro Mac(a) begin x := \A i \in {1} : i > 0 ;
                      y := \A i \in {1} : i > 0 ;
                      z := \A i \in {1} : i > 0 ;
                      assert /\ \A i \in {1} : i > 0 
                             /\ \A i \in {1} : i > 0 
                             /\ \A i \in {1} : i > 0  ;
                      assert a 
   end macro;
     
   procedure P(a = /\ \A i \in {1} : i > 0 
                   /\ \A i \in {1} : i > 0 
                   /\ \A i \in {1} : i > 0)
      begin P1: x := \A i \in {1} : i > 0 ;
                y := \A i \in {1} : i > 0 ;
                z := \A i \in {1} : i > 0 ;
                return
      end procedure
   process Q \in {qq \in {1,2} : /\ \A i \in {1} : i > 0 
                                 /\ \A j \in {1} : j > 0 
                                 /\ \A k \in {1} : k > 0 }
     variable w = /\ \A i \in {1} : i > 0 
                  /\ \A i \in {1} : i > 0 
                  /\ \A i \in {1} : i > 0 
      begin P1: if /\ \A i \in {1} : i > 0 
                   /\ \A i \in {1} : i > 0 
                   /\ \A i \in {1} : i > 0  then x := \A i \in {1} : i > 0 ;
                                                 y := \A i \in {1} : i > 0 ;
                                                 z := \A i \in {1} : i > 0 
                  else x := \A i \in {1} : i > 0 ;
                       y := \A i \in {1} : i > 0 ;
                       z := \A i \in {1} : i > 0                       
                 end if ;
           P15:  with k  \in {kk \in {2,3} : /\ \A i \in {1} : i > 0 
                                             /\ \A i \in {1} : i > 0 
                                             /\ \A i \in {1} : i > 0 } do
                   with m = /\ \A i \in {1} : i > 0 
                            /\ \A i \in {1} : i > 0 
                            /\ \A i \in {1} : i > 0  do
                    x := \A i \in {1} : i > 0 ;
                    y := \A i \in {1} : i > 0 ;
                    z := \A i \in {1} : i > 0  
                 end with end with ;
            P2: while /\ \A i \in {1} : i > 0 
                      /\ \A i \in {1} : i > 0 
                      /\ \A i \in {1} : i > 0 
                      /\ FALSE do
                   x := \A i \in {1} : i > 0 ;
                   y := \A i \in {1} : i > 0 ;
                   z := \A i \in {1} : i > 0 ;
                   w := /\ \A i \in {1} : i > 0 
                        /\ \A i \in {1} : i > 0 
                        /\ \A i \in {1} : i > 0 
                end while ;
            P3: call P(/\ \A i \in {1} : i > 0 
                       /\ \A i \in {1} : i > 0 
                       /\ \A i \in {1} : i > 0) ;
            P4: assert /\ \A i \in {1} : i > 0 
                       /\ \A i \in {1} : i > 0 
                       /\ \A i \in {1} : i > 0 ;
                print  /\ \A i \in {1} : i > 0 
                       /\ \A i \in {1} : i > 0 
                       /\ \A i \in {1} : i > 0 ;
            P5: Mac(/\ \A i \in {1} : i > 0 
                    /\ \A i \in {1} : i > 0 
                    /\ \A i \in {1} : i > 0 )
     end process
   end algorithm

----------- MODULE bug_06_01_25 -----------
EXTENDS Sequences, Naturals, TLC

ASSUME \forall i \in {} : i \geq 1

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9ef67f07b10dbbf43fc7d4cb2d8d7b02
\* Label P1 of procedure P at line 22 col 17 changed to P1_
CONSTANT defaultInitValue
VARIABLES x, y, z, pc, stack

(* define statement *)
foo == /\ \A i \in {1} : i > 0
       /\ \A i \in {1} : i > 0
       /\ \A i \in {1} : i > 0

VARIABLES a, w

vars == << x, y, z, pc, stack, a, w >>

ProcSet == ({qq \in {1,2} : /\ \A i \in {1} : i > 0
                            /\ \A j \in {1} : j > 0
                            /\ \A k \in {1} : k > 0 })

Init == (* Global variables *)
        /\ x = defaultInitValue
        /\ y = defaultInitValue
        /\ z = (/\ \A i \in {1} : i > 0
                /\ \A i \in {1} : i > 0
                /\ \A i \in {1} : i > 0)
        (* Procedure P *)
        /\ a = [ self \in ProcSet |-> /\ \A i \in {1} : i > 0
                                      /\ \A i \in {1} : i > 0
                                      /\ \A i \in {1} : i > 0]
        (* Process Q *)
        /\ w = [self \in {qq \in {1,2} : /\ \A i \in {1} : i > 0
                                         /\ \A j \in {1} : j > 0
                                         /\ \A k \in {1} : k > 0 } |-> /\ \A i \in {1} : i > 0
                                                                       /\ \A i \in {1} : i > 0
                                                                       /\ \A i \in {1} : i > 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "P1"]

P1_(self) == /\ pc[self] = "P1_"
             /\ x' = (\A i \in {1} : i > 0)
             /\ y' = (\A i \in {1} : i > 0)
             /\ z' = (\A i \in {1} : i > 0)
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ a' = [a EXCEPT ![self] = Head(stack[self]).a]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ w' = w

P(self) == P1_(self)

P1(self) == /\ pc[self] = "P1"
            /\ IF /\ \A i \in {1} : i > 0
                  /\ \A i \in {1} : i > 0
                  /\ \A i \in {1} : i > 0
                  THEN /\ x' = (\A i \in {1} : i > 0)
                       /\ y' = (\A i \in {1} : i > 0)
                       /\ z' = (\A i \in {1} : i > 0)
                  ELSE /\ x' = (\A i \in {1} : i > 0)
                       /\ y' = (\A i \in {1} : i > 0)
                       /\ z' = (\A i \in {1} : i > 0)
            /\ pc' = [pc EXCEPT ![self] = "P15"]
            /\ UNCHANGED << stack, a, w >>

P15(self) == /\ pc[self] = "P15"
             /\ \E k \in {kk \in {2,3} : /\ \A i \in {1} : i > 0
                                         /\ \A i \in {1} : i > 0
                                         /\ \A i \in {1} : i > 0 }:
                  LET m == /\ \A i \in {1} : i > 0
                           /\ \A i \in {1} : i > 0
                           /\ \A i \in {1} : i > 0 IN
                    /\ x' = (\A i \in {1} : i > 0)
                    /\ y' = (\A i \in {1} : i > 0)
                    /\ z' = (\A i \in {1} : i > 0)
             /\ pc' = [pc EXCEPT ![self] = "P2"]
             /\ UNCHANGED << stack, a, w >>

P2(self) == /\ pc[self] = "P2"
            /\ IF /\ \A i \in {1} : i > 0
                  /\ \A i \in {1} : i > 0
                  /\ \A i \in {1} : i > 0
                  /\ FALSE
                  THEN /\ x' = (\A i \in {1} : i > 0)
                       /\ y' = (\A i \in {1} : i > 0)
                       /\ z' = (\A i \in {1} : i > 0)
                       /\ w' = [w EXCEPT ![self] = /\ \A i \in {1} : i > 0
                                                   /\ \A i \in {1} : i > 0
                                                   /\ \A i \in {1} : i > 0]
                       /\ pc' = [pc EXCEPT ![self] = "P2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "P3"]
                       /\ UNCHANGED << x, y, z, w >>
            /\ UNCHANGED << stack, a >>

P3(self) == /\ pc[self] = "P3"
            /\ /\ a' = [a EXCEPT ![self] = /\ \A i \in {1} : i > 0
                                           /\ \A i \in {1} : i > 0
                                           /\ \A i \in {1} : i > 0]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "P",
                                                        pc        |->  "P4",
                                                        a         |->  a[self] ] >>
                                                    \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "P1_"]
            /\ UNCHANGED << x, y, z, w >>

P4(self) == /\ pc[self] = "P4"
            /\ Assert(/\ \A i \in {1} : i > 0
                      /\ \A i \in {1} : i > 0
                      /\ \A i \in {1} : i > 0, 
                      "Failure of assertion at line 66, column 17.")
            /\ PrintT(/\ \A i \in {1} : i > 0
                      /\ \A i \in {1} : i > 0
                      /\ \A i \in {1} : i > 0)
            /\ pc' = [pc EXCEPT ![self] = "P5"]
            /\ UNCHANGED << x, y, z, stack, a, w >>

P5(self) == /\ pc[self] = "P5"
            /\ x' = (\A i \in {1} : i > 0)
            /\ y' = (\A i \in {1} : i > 0)
            /\ z' = (\A i \in {1} : i > 0)
            /\ Assert(/\ \A i \in {1} : i > 0
                      /\ \A i \in {1} : i > 0
                      /\ \A i \in {1} : i > 0, 
                      "Failure of assertion at line 13, column 23 of macro called at line 72, column 17.")
            /\ Assert(/\ \A i \in {1} : i > 0
                      /\ \A i \in {1} : i > 0
                      /\ \A i \in {1} : i > 0, 
                      "Failure of assertion at line 16, column 23 of macro called at line 72, column 17.")
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << stack, a, w >>

Q(self) == P1(self) \/ P15(self) \/ P2(self) \/ P3(self) \/ P4(self)
              \/ P5(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: P(self))
           \/ (\E self \in {qq \in {1,2} : /\ \A i \in {1} : i > 0
                                           /\ \A j \in {1} : j > 0
                                           /\ \A k \in {1} : k > 0 }: Q(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c0ae8bdf7ad8a969ed412d1b64210cb9
========================================
