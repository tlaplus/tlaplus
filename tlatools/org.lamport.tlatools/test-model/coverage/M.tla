------------------------------ MODULE M ------------------------------
EXTENDS Naturals, FiniteSets

VARIABLES active, color, tpos, tcolor
vars == <<active, color, tpos, tcolor>>

Nodes == 0 .. 2
Color == {"white", "black"}

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]    \* status of nodes (active or passive)
  /\ color \in [Nodes -> Color]       \* color of nodes
  /\ tpos \in Nodes                   \* token position
  /\ tcolor \in Color                 \* token color

Init ==
  /\ active \in [{23,42,56} -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos \in Nodes
  /\ tcolor = "black"

Next ==
  /\ active' \in [{23,42,56} -> BOOLEAN]
  /\ color' \in [Nodes -> Color]
  /\ tpos' \in Nodes
  /\ tcolor' = "black"
  
Spec ==
  Init /\ [][Next]_vars

============
