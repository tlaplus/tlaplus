Plus Cal options (-wf -spec PlusCal2)
----------------------------- MODULE Fischer    ----------------------------- 
EXTENDS Naturals, TLC
\* what's up 
CONSTANT Delta, Epsilon  \* The timing delays  
CONSTANT N   \* The number of synchronizing processes
\* CONSTANT defaultInitValue

ASSUME /\ Print("Testing Fischer's Mutual Exclusion Algorithm", TRUE)
       /\ Print(<<" Number of processes = ", N>>, TRUE)
       /\ Print(<<" Delta   = ", Delta>>, TRUE)
       /\ Print(<<" Epsilon = ", Epsilon>>, TRUE)
       /\ Print("Should find a bug if N > 1 and Delta >= Epsilon", TRUE)


Infinity == 9999999

(**********************
--algorithm Fischer
  variables x = 0 ; timer = [i \in 1..N |-> Infinity] ;
  process Proc \in 1..N
   variable firstTime = TRUE ;
   begin a : while TRUE             
     (**********************************************************************)
     (* Note that the +cal syntax requires that both while statements be   *)
     (* labeled, adding a useless atomic action.  The only ways I see to   *)
     (* eliminate that would be by adding a "goto" statement that could be *)
     (* used to encode the inner "while" loop.                             *)
     (**********************************************************************)
              do b : while x # self  
                        (***************************************************)
                        (* x can't equal i the first time through the loop *)
                        (***************************************************)
                       do c : when x = 0 ;
                              timer[self] := Delta ;
                          d : x := self ; 
                              timer[self] := Epsilon ;
                          e : when timer[self] = 0 ;
                              timer[self] := Infinity ;
                     end while ; 
                cs : skip ;  \* critical section
                 f : x := 0 ;
             end while ;
   end process  
  process Tick = 0
    begin t1 : while TRUE
                 do when \A i \in 1..N : timer[i] > 0 ;
                    timer := [i \in 1..N |-> IF timer[i] < Infinity
                                           THEN timer[i] - 1 
                                           ELSE timer[i] ] ;
               end while ;
   end process
end algorithm

***********************)

\* BEGIN TRANSLATION (chksum(pcal) = "36cd5b05" /\ chksum(tla) = "6f1c46e")
VARIABLES pc, x, timer, firstTime

vars == << pc, x, timer, firstTime >>

ProcSet == (1..N) \cup {0}

Init == (* Global variables *)
        /\ x = 0
        /\ timer = [i \in 1..N |-> Infinity]
        (* Process Proc *)
        /\ firstTime = [self \in 1..N |-> TRUE]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..N -> "a"
                                        [] self = 0 -> "t1"]

a(self) == /\ pc[self] = "a"
           /\ pc' = [pc EXCEPT ![self] = "b"]
           /\ UNCHANGED << x, timer, firstTime >>

b(self) == /\ pc[self] = "b"
           /\ IF x # self
                 THEN /\ pc' = [pc EXCEPT ![self] = "c"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
           /\ UNCHANGED << x, timer, firstTime >>

c(self) == /\ pc[self] = "c"
           /\ x = 0
           /\ timer' = [timer EXCEPT ![self] = Delta]
           /\ pc' = [pc EXCEPT ![self] = "d"]
           /\ UNCHANGED << x, firstTime >>

d(self) == /\ pc[self] = "d"
           /\ x' = self
           /\ timer' = [timer EXCEPT ![self] = Epsilon]
           /\ pc' = [pc EXCEPT ![self] = "e"]
           /\ UNCHANGED firstTime

e(self) == /\ pc[self] = "e"
           /\ timer[self] = 0
           /\ timer' = [timer EXCEPT ![self] = Infinity]
           /\ pc' = [pc EXCEPT ![self] = "b"]
           /\ UNCHANGED << x, firstTime >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "f"]
            /\ UNCHANGED << x, timer, firstTime >>

f(self) == /\ pc[self] = "f"
           /\ x' = 0
           /\ pc' = [pc EXCEPT ![self] = "a"]
           /\ UNCHANGED << timer, firstTime >>

Proc(self) == a(self) \/ b(self) \/ c(self) \/ d(self) \/ e(self)
                 \/ cs(self) \/ f(self)

t1 == /\ pc[0] = "t1"
      /\ \A i \in 1..N : timer[i] > 0
      /\ timer' = [i \in 1..N |-> IF timer[i] < Infinity
                                THEN timer[i] - 1
                                ELSE timer[i] ]
      /\ pc' = [pc EXCEPT ![0] = "t1"]
      /\ UNCHANGED << x, firstTime >>

Tick == t1

Next == Tick
           \/ (\E self \in 1..N: Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(Proc(self))
        /\ WF_vars(Tick)

\* END TRANSLATION

inCS(i) ==  pc[i] = "cs"

Invariant == \A i, k \in 1..N : (i # k) => ~ (inCS(i) /\ inCS(k))

Liveness == []<> \E i \in 1..N : inCS(i)
=============================================================================
