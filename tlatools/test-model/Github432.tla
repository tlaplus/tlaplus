---- MODULE Github432 ----

EXTENDS TLC

CONSTANT Humans, Others

symmetry == Permutations(Humans) \union Permutations(Others)

VARIABLES set

TypeOK ==
    /\ set \subseteq Humans

Init ==
    /\ set = {}

Next ==
    \E h \in Humans:
        set' = set \union {h}

==================================

