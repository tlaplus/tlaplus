----------------------------- MODULE Github1487 -----------------------------
EXTENDS Naturals

VARIABLES sub, uni, cup, cap, dif, fcns, rcds, tups, pred, fcn, i, k

\* Each of these is a lazy value that TLC converts only when needed. Neither
\* operand of \cup, \cap, and \ is an enumerated set, which TLC would reduce
\* right away.
Init == /\ sub = SUBSET {0, 1}
        /\ uni = UNION SUBSET {0, 1}
        /\ cup = SUBSET {0, 1} \cup SUBSET {2}
        /\ cap = SUBSET {0, 1} \cap SUBSET {1, 2}
        /\ dif = SUBSET {0, 1} \ SUBSET {1}
        /\ fcns = [{0, 1} -> {0, 1}]
        /\ rcds = [a : {0, 1}]
        /\ tups = {0, 1} \X {0, 1}
        /\ pred = {x \in SUBSET {0, 1} : 0 \notin x}
        /\ fcn = [x \in SUBSET {0, 1} |-> x]
        /\ i = 0
        /\ k \in 1..64

Next == /\ i < 3
        /\ i' = i + 1
        /\ UNCHANGED <<sub, uni, cup, cap, dif, fcns, rcds, tups, pred, fcn, k>>

\* The view does not fingerprint the lazy values, which therefore remain lazy
\* until the DiskStateQueue writes them to disk.
View == <<i, k>>

\* Membership does not convert the lazy values.
Inv == /\ {0} \in sub /\ {2} \notin sub
       /\ 1 \in uni /\ 2 \notin uni
       /\ {2} \in cup /\ {0, 2} \notin cup
       /\ {1} \in cap /\ {0} \notin cap
       /\ {0} \in dif /\ {1} \notin dif
       /\ [x \in {0, 1} |-> 0] \in fcns /\ [x \in {0, 1} |-> 2] \notin fcns
       /\ [a |-> 1] \in rcds /\ [a |-> 2] \notin rcds
       /\ <<0, 1>> \in tups /\ <<1, 2>> \notin tups
       /\ {1} \in pred /\ {0} \notin pred
       /\ \A x \in DOMAIN fcn : fcn[x] = x
=============================================================================
