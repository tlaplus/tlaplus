---------------------------- MODULE InitStateBug ----------------------------
EXTENDS Naturals

RECURSIVE AllSubs(_)
AllSubs(S) ==
  IF S = {} THEN {{}} ELSE
  LET
    c  == CHOOSE c \in S : TRUE
    T  == S \ {c}
    TT == AllSubs(T)
  IN
    TT \cup { t \cup {c} : t \in TT }

RECURSIVE Sum(_)
Sum(S) ==
  IF S = {} THEN 0 ELSE
  LET c == CHOOSE c \in S : TRUE
  IN c + Sum(S \ {c})

Ch(S) == CHOOSE v \in S : Sum(v) > 4

S1 == SUBSET (1..20) \* Increased from 1..8 to 1..20 to also test performance with this spec.
S2 == AllSubs(1..8)

VARIABLE pc, set, fun

Init == pc = 0 /\ set = {} /\ fun = {}

Next ==
  CASE
  pc = 0 -> pc' = 1 /\ set' = S1 /\ fun' = Ch(set')
  []
  pc = 1 -> pc' = 2 /\ set' = S2 /\ fun' = Ch(set')
  []
  OTHER -> FALSE
=============================================================================
\* Modification History
\* Last modified Wed Mar 07 10:27:18 PST 2012 by tomr
\* Created Wed Mar 07 10:24:35 PST 2012 by tomr
