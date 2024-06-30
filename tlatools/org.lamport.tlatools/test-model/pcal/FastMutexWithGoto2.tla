------------------------ MODULE FastMutexWithGoto2 -------------------------- 

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat

(**********************
--algorithm FastMutex
  variables x = 0 ; y = 0 ; b = [i \in 1..N |-> FALSE] ; 
process Proc \in 1..N
variables S = {} ; 
begin
start : while TRUE
         do l1 : b[self] := TRUE ;
            l2 : x := self ;
            l3 : if y # 0
                   then l4 : b[self] := FALSE ;
                        l5 : when y = 0 ; 
                             goto start ;
                 end if ;
            l6 : y := self ;
            l7 : if x # self 
                   then l8 : b[self] := FALSE ;
                             S := 1..N \ {self} ;
                        l9 : while S # {} do
                              with j \in S do when ~b[j] ;
                                     S := S \ {j}
                              end with ;
                             end while ;
                       l10 : if y # self then l11 : when y = 0 ;
                                                    goto start ;
                             end if ;
                 end if;
             cs : skip ; \* the critical section
            l12 : y := 0 ;
            l13 : b[self] := FALSE ;
        end while ;
end process
end algorithm

***********************)

\* BEGIN TRANSLATION (chksum(pcal) = "f52892c0" /\ chksum(tla) = "b02a536c")
VARIABLES pc, x, y, b, S

vars == << pc, x, y, b, S >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        (* Process Proc *)
        /\ S = [self \in 1..N |-> {}]
        /\ pc = [self \in ProcSet |-> "start"]

start(self) == /\ pc[self] = "start"
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << x, y, b, S >>

l1(self) == /\ pc[self] = "l1"
            /\ b' = [b EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << x, y, S >>

l2(self) == /\ pc[self] = "l2"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED << y, b, S >>

l3(self) == /\ pc[self] = "l3"
            /\ IF y # 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "l4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << x, y, b, S >>

l4(self) == /\ pc[self] = "l4"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << x, y, S >>

l5(self) == /\ pc[self] = "l5"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, S >>

l6(self) == /\ pc[self] = "l6"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l7"]
            /\ UNCHANGED << x, b, S >>

l7(self) == /\ pc[self] = "l7"
            /\ IF x # self
                  THEN /\ pc' = [pc EXCEPT ![self] = "l8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, S >>

l8(self) == /\ pc[self] = "l8"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ S' = [S EXCEPT ![self] = 1..N \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "l9"]
            /\ UNCHANGED << x, y >>

l9(self) == /\ pc[self] = "l9"
            /\ IF S[self] # {}
                  THEN /\ \E j \in S[self]:
                            /\ ~b[j]
                            /\ S' = [S EXCEPT ![self] = S[self] \ {j}]
                       /\ pc' = [pc EXCEPT ![self] = "l9"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l10"]
                       /\ S' = S
            /\ UNCHANGED << x, y, b >>

l10(self) == /\ pc[self] = "l10"
             /\ IF y # self
                   THEN /\ pc' = [pc EXCEPT ![self] = "l11"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << x, y, b, S >>

l11(self) == /\ pc[self] = "l11"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, S >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l12"]
            /\ UNCHANGED << x, y, b, S >>

l12(self) == /\ pc[self] = "l12"
             /\ y' = 0
             /\ pc' = [pc EXCEPT ![self] = "l13"]
             /\ UNCHANGED << x, b, S >>

l13(self) == /\ pc[self] = "l13"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, S >>

Proc(self) == start(self) \/ l1(self) \/ l2(self) \/ l3(self) \/ l4(self)
                 \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self)
                 \/ l9(self) \/ l10(self) \/ l11(self) \/ cs(self)
                 \/ l12(self) \/ l13(self)

Next == (\E self \in 1..N: Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION

inCS(i) ==  (pc[i] = "cs") 

Invariant == \A i, k \in 1..N : (i # k) => ~ (inCS(i) /\ inCS(k))


Liveness == []<> \E i \in 1..N : inCS(i)
=============================================================================
