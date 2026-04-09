---- MODULE SubseteqNextState ----
EXTENDS TLC
VARIABLES x, y
TypeOK == x \subseteq {1, 2, 3}
Inv ==
  /\ ENABLED (x' \subseteq {1})
  /\ y = {1, 2, 3}
Init ==
  /\ x \subseteq {1, 2}
  /\ y = {1, 2, 3}
Next ==
  /\ UNCHANGED y
  /\ x' \subseteq y'

FullSet == x = {1, 2, 3}

GainThree == 3 \in x' /\ 3 \notin x

PossibleCounts ==
    LET p == TLCGet("all:named")["s:_possible"][1]
    IN /\ p["FullSet"] = 8
       /\ p["GainThree"] = 16
====
