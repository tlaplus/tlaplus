------------------------- MODULE FastMutexWithGoto -------------------------- 

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat

(**********************
--algorithm FastMutex
variables x = 0 ; y = 0 ; b = [i \in 1..N |-> FALSE] ; 

process Proc \in 1..N
  variables j = 0 ; 
  begin
    ncs: while TRUE do 
              skip ;  \* Noncritical section.
       start: b[self] := TRUE ;
          l1: x := self ;
          l2: if y # 0
                then l3: b[self] := FALSE ;
                     l4: when y = 0 ; 
                          goto start ;
              end if ;
          l5: y := self ;
          l6: if x # self 
                then l7: b[self] := FALSE ;
                         j := 1 ;
                     l8: while j \leq N do 
                           when ~b[j] ;
                           j := j+1 ;
                         end while ;
                     l9: if y # self then l10: when y = 0 ;
                         goto start ;
                           end if ;
               end if;
          cs: skip ; \* the critical section
         l11: y := 0 ;
         l12: b[self] := FALSE ;
         end while ;
end process

end algorithm

***********************)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-765a4c9fba722b8f4115732919fba3a0
VARIABLES x, y, b, pc, j

vars == << x, y, b, pc, j >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        (* Process Proc *)
        /\ j = [self \in 1..N |-> 0]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j >>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << x, y, j >>

l1(self) == /\ pc[self] = "l1"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << y, b, j >>

l2(self) == /\ pc[self] = "l2"
            /\ IF y # 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "l3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << x, y, b, j >>

l3(self) == /\ pc[self] = "l3"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED << x, y, j >>

l4(self) == /\ pc[self] = "l4"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j >>

l5(self) == /\ pc[self] = "l5"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << x, b, j >>

l6(self) == /\ pc[self] = "l6"
            /\ IF x # self
                  THEN /\ pc' = [pc EXCEPT ![self] = "l7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j >>

l7(self) == /\ pc[self] = "l7"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l8"]
            /\ UNCHANGED << x, y >>

l8(self) == /\ pc[self] = "l8"
            /\ IF j[self] \leq N
                  THEN /\ ~b[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self]+1]
                       /\ pc' = [pc EXCEPT ![self] = "l8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
                       /\ j' = j
            /\ UNCHANGED << x, y, b >>

l9(self) == /\ pc[self] = "l9"
            /\ IF y # self
                  THEN /\ pc' = [pc EXCEPT ![self] = "l10"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j >>

l10(self) == /\ pc[self] = "l10"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l11"]
            /\ UNCHANGED << x, y, b, j >>

l11(self) == /\ pc[self] = "l11"
             /\ y' = 0
             /\ pc' = [pc EXCEPT ![self] = "l12"]
             /\ UNCHANGED << x, b, j >>

l12(self) == /\ pc[self] = "l12"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << x, y, j >>

Proc(self) == ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
                 \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self)
                 \/ l8(self) \/ l9(self) \/ l10(self) \/ cs(self)
                 \/ l11(self) \/ l12(self)

Next == (\E self \in 1..N: Proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-556f4fffd8fac96ddb09d8c9c984f878

inCS(i) ==  (pc[i] = "cs") 

Invariant == \A i, k \in 1..N: (i # k) => ~ (inCS(i) /\ inCS(k))

Liveness == []<> \E i \in 1..N: inCS(i)

CondLiveness == ([]<> \E i \in 1..N : pc[i] # "ncs") => Liveness

Fairness == \A i \in 1..N : 
               /\ WF_vars(start(i))
               /\ WF_vars(l1(i))
               /\ WF_vars(l2(i))
               /\ WF_vars(l3(i))
               /\ WF_vars(l4(i))
               /\ WF_vars(l5(i))
               /\ WF_vars(l6(i))
               /\ WF_vars(l7(i))
               /\ WF_vars(l8(i))
               /\ WF_vars(l9(i))
               /\ WF_vars(l10(i))
               /\ WF_vars(l11(i))
               /\ WF_vars(l12(i))
FairSpec == Spec /\ Fairness
=============================================================================
