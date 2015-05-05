------------------------------- MODULE EWD840 -------------------------------
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor
Nodes == 0 .. N-1
Color == {"white", "black"}

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos \in Nodes
  /\ tcolor \in Color

(* Initially the token is at node 0, and it is black. There
   are no constraints on the status and color of the nodes. *)
Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos = 0
  /\ tcolor = "black"

InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = "black" \/ color[0] = "black"
  /\ tpos' = N-1
  /\ tcolor' = "white"
  /\ color' = [color EXCEPT ![0] = "white"]
  /\ UNCHANGED <<active>>

PassToken(i) == 
  /\ tpos = i
  /\ ~ active[i]
        \/ color[i] = "black"
        \/ tcolor = "black"
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active>>

SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Nodes \ {i} :
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
  /\ UNCHANGED <<tpos, tcolor>>

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tpos, tcolor>>

Next ==
  \/ InitiateProbe
  \/ \E i \in Nodes \ {0} : PassToken(i)
  \/ \E i \in Nodes : SendMsg(i) \/ Deactivate(i)

System ==
  \/ InitiateProbe
  \/ \E i \in Nodes \ {0} : PassToken(i)

vars == <<active, color, tpos, tcolor>>

Fairness == WF_vars(System)

Spec == Init /\ [][Next]_vars (*/\ Fairness*)

LInv == [][Next]_vars => WF_vars(System)

-----------------------------------------------------------------------------

NeverBlack == \A i \in Nodes : color[i] # "black"

NeverChangeColor == [][ \A i \in Nodes : UNCHANGED color[i] ]_vars

terminationDetected ==
  /\ tpos = 0 /\ tcolor = "white"
  /\ color[0] = "white" /\ ~ active[0]
  /\ color[1] = "white"

TerminationDetection ==
  terminationDetected => \A i \in Nodes : ~ active[i]

Liveness ==
  /\ (\A i \in Nodes : ~ active[i]) ~> terminationDetected

AllNodesTerminateIfNoMessages ==
  <>[][~ \E i \in Nodes : SendMsg(i)]_vars
  => <>(\A i \in Nodes : ~ active[i])

Inv == 
  \/ P0:: \A i \in Nodes : tpos < i => ~ active[i]
  \/ P1:: \E j \in 0 .. tpos : color[j] = "black"
  \/ P2:: tcolor = "black"

=============================================================================
