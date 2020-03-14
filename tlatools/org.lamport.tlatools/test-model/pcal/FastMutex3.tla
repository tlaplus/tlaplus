----------------------------- MODULE FastMutex3 ----------------------------- 

\* This tests the translation when there are two different processes

EXTENDS Naturals, TLC

CONSTANT N

ASSUME (N \in Nat) 

(**********************
--algorithm FastMutex
  variables x = 0 ; y = 0 ; b = [i \in 1..N |-> FALSE] ; 
process Proc1 = 1
variables j = 0 ; failed = FALSE ; 
begin
start : while TRUE
         do l1 : b[1] := TRUE ;
            l2 : x := 1 ;
            l3 : if y # 0
                   then l4 : b[1] := FALSE ;
                        l5 : when y = 0 ; skip ;
                   else l6 : y := 1 ;
                        l7 : if x # 1 
                               then l8 : b[1] := FALSE ;
                                         j := 1 ;
                                    l9 : while (j \leq N)
                                           do when ~b[j] ;
                                              j := j+1 ;
                                         end while ;
                                    l10 : if y # 1
                                            then when y = 0 ;
                                                 failed := TRUE ;
                                          end if;
                             end if ;
                        cs : if ~ failed
                               then       skip ; \* the critical section
                                    l11 : y := 0 ;
                                    l12 : b[1] := FALSE ;
                               else failed := FALSE ;
                             end if ;
                  end if ;
        end while ;
end process
process Proc2 \in 2..N
variables j2 = 0 ; failed2 = FALSE ; 
begin
2start : while TRUE
         do 2l1 : b[self] := TRUE ;
            2l2 : x := self ;
            2l3 : if y # 0
                   then 2l4 : b[self] := FALSE ;
                        2l5 : when y = 0 ; skip ;
                   else 2l6 : y := self ;
                        2l7 : if x # self 
                               then 2l8 : b[self] := FALSE ;
                                         j2 := 1 ;
                                    2l9 : while (j2 \leq N)
                                           do when ~b[j2] ;
                                              j2 := j2+1 ;
                                         end while ;
                                    2l10 : if y # self
                                            then when y = 0 ;
                                                 failed2 := TRUE ;
                                          end if;
                             end if ;
                        2cs : if ~ failed2
                               then       skip ; \* the critical section
                                    2l11 : y := 0 ;
                                    2l12 : b[self] := FALSE ;
                               else failed2 := FALSE ;
                             end if ;
                  end if ;
        end while ;
end process
end algorithm

***********************)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-1901ed6bf685f13ebc84143ab4ef5b13
VARIABLES x, y, b, pc, j, failed, j2, failed2

vars == << x, y, b, pc, j, failed, j2, failed2 >>

ProcSet == {1} \cup (2..N)

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        (* Process Proc1 *)
        /\ j = 0
        /\ failed = FALSE
        (* Process Proc2 *)
        /\ j2 = [self \in 2..N |-> 0]
        /\ failed2 = [self \in 2..N |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "start"
                                        [] self \in 2..N -> "2start"]

start == /\ pc[1] = "start"
         /\ pc' = [pc EXCEPT ![1] = "l1"]
         /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l1 == /\ pc[1] = "l1"
      /\ b' = [b EXCEPT ![1] = TRUE]
      /\ pc' = [pc EXCEPT ![1] = "l2"]
      /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

l2 == /\ pc[1] = "l2"
      /\ x' = 1
      /\ pc' = [pc EXCEPT ![1] = "l3"]
      /\ UNCHANGED << y, b, j, failed, j2, failed2 >>

l3 == /\ pc[1] = "l3"
      /\ IF y # 0
            THEN /\ pc' = [pc EXCEPT ![1] = "l4"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "l6"]
      /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l4 == /\ pc[1] = "l4"
      /\ b' = [b EXCEPT ![1] = FALSE]
      /\ pc' = [pc EXCEPT ![1] = "l5"]
      /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

l5 == /\ pc[1] = "l5"
      /\ y = 0
      /\ TRUE
      /\ pc' = [pc EXCEPT ![1] = "start"]
      /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l6 == /\ pc[1] = "l6"
      /\ y' = 1
      /\ pc' = [pc EXCEPT ![1] = "l7"]
      /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

l7 == /\ pc[1] = "l7"
      /\ IF x # 1
            THEN /\ pc' = [pc EXCEPT ![1] = "l8"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "cs"]
      /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l8 == /\ pc[1] = "l8"
      /\ b' = [b EXCEPT ![1] = FALSE]
      /\ j' = 1
      /\ pc' = [pc EXCEPT ![1] = "l9"]
      /\ UNCHANGED << x, y, failed, j2, failed2 >>

l9 == /\ pc[1] = "l9"
      /\ IF (j \leq N)
            THEN /\ ~b[j]
                 /\ j' = j+1
                 /\ pc' = [pc EXCEPT ![1] = "l9"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "l10"]
                 /\ j' = j
      /\ UNCHANGED << x, y, b, failed, j2, failed2 >>

l10 == /\ pc[1] = "l10"
       /\ IF y # 1
             THEN /\ y = 0
                  /\ failed' = TRUE
             ELSE /\ TRUE
                  /\ UNCHANGED failed
       /\ pc' = [pc EXCEPT ![1] = "cs"]
       /\ UNCHANGED << x, y, b, j, j2, failed2 >>

cs == /\ pc[1] = "cs"
      /\ IF ~ failed
            THEN /\ TRUE
                 /\ pc' = [pc EXCEPT ![1] = "l11"]
                 /\ UNCHANGED failed
            ELSE /\ failed' = FALSE
                 /\ pc' = [pc EXCEPT ![1] = "start"]
      /\ UNCHANGED << x, y, b, j, j2, failed2 >>

l11 == /\ pc[1] = "l11"
       /\ y' = 0
       /\ pc' = [pc EXCEPT ![1] = "l12"]
       /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

l12 == /\ pc[1] = "l12"
       /\ b' = [b EXCEPT ![1] = FALSE]
       /\ pc' = [pc EXCEPT ![1] = "start"]
       /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

Proc1 == start \/ l1 \/ l2 \/ l3 \/ l4 \/ l5 \/ l6 \/ l7 \/ l8 \/ l9 \/ l10
            \/ cs \/ l11 \/ l12

2start(self) == /\ pc[self] = "2start"
                /\ pc' = [pc EXCEPT ![self] = "2l1"]
                /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

2l1(self) == /\ pc[self] = "2l1"
             /\ b' = [b EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "2l2"]
             /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

2l2(self) == /\ pc[self] = "2l2"
             /\ x' = self
             /\ pc' = [pc EXCEPT ![self] = "2l3"]
             /\ UNCHANGED << y, b, j, failed, j2, failed2 >>

2l3(self) == /\ pc[self] = "2l3"
             /\ IF y # 0
                   THEN /\ pc' = [pc EXCEPT ![self] = "2l4"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "2l6"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

2l4(self) == /\ pc[self] = "2l4"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "2l5"]
             /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

2l5(self) == /\ pc[self] = "2l5"
             /\ y = 0
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "2start"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

2l6(self) == /\ pc[self] = "2l6"
             /\ y' = self
             /\ pc' = [pc EXCEPT ![self] = "2l7"]
             /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

2l7(self) == /\ pc[self] = "2l7"
             /\ IF x # self
                   THEN /\ pc' = [pc EXCEPT ![self] = "2l8"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "2cs"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

2l8(self) == /\ pc[self] = "2l8"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ j2' = [j2 EXCEPT ![self] = 1]
             /\ pc' = [pc EXCEPT ![self] = "2l9"]
             /\ UNCHANGED << x, y, j, failed, failed2 >>

2l9(self) == /\ pc[self] = "2l9"
             /\ IF (j2[self] \leq N)
                   THEN /\ ~b[j2[self]]
                        /\ j2' = [j2 EXCEPT ![self] = j2[self]+1]
                        /\ pc' = [pc EXCEPT ![self] = "2l9"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "2l10"]
                        /\ j2' = j2
             /\ UNCHANGED << x, y, b, j, failed, failed2 >>

2l10(self) == /\ pc[self] = "2l10"
              /\ IF y # self
                    THEN /\ y = 0
                         /\ failed2' = [failed2 EXCEPT ![self] = TRUE]
                    ELSE /\ TRUE
                         /\ UNCHANGED failed2
              /\ pc' = [pc EXCEPT ![self] = "2cs"]
              /\ UNCHANGED << x, y, b, j, failed, j2 >>

2cs(self) == /\ pc[self] = "2cs"
             /\ IF ~ failed2[self]
                   THEN /\ TRUE
                        /\ pc' = [pc EXCEPT ![self] = "2l11"]
                        /\ UNCHANGED failed2
                   ELSE /\ failed2' = [failed2 EXCEPT ![self] = FALSE]
                        /\ pc' = [pc EXCEPT ![self] = "2start"]
             /\ UNCHANGED << x, y, b, j, failed, j2 >>

2l11(self) == /\ pc[self] = "2l11"
              /\ y' = 0
              /\ pc' = [pc EXCEPT ![self] = "2l12"]
              /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

2l12(self) == /\ pc[self] = "2l12"
              /\ b' = [b EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "2start"]
              /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

Proc2(self) == 2start(self) \/ 2l1(self) \/ 2l2(self) \/ 2l3(self)
                  \/ 2l4(self) \/ 2l5(self) \/ 2l6(self) \/ 2l7(self)
                  \/ 2l8(self) \/ 2l9(self) \/ 2l10(self) \/ 2cs(self)
                  \/ 2l11(self) \/ 2l12(self)

Next == Proc1
           \/ (\E self \in 2..N: Proc2(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Proc1)
        /\ \A self \in 2..N : WF_vars(Proc2(self))

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-35555ac3cdd01367ca89de83ceeebd64

ASSUME Print(<<"ProcSet =" , ProcSet>>, TRUE)
inCS(i) ==  IF i = 1 THEN (pc[i] = "cs") /\ (~failed)
                     ELSE (pc[i] = "2cs") /\ (~failed2[i])
Invariant == \A i, k \in 1..N : (i # k) => ~ (inCS(i) /\ inCS(k))

Liveness == []<> \E i \in 1..N : inCS(i)
=============================================================================
