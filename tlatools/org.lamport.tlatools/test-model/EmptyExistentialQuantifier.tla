--------------------------- MODULE EmptyExistentialQuantifier --------------
VARIABLE N

Init == N = 1

Next == \E i \in {} : UNCHANGED N             \* \E i \in {}: ... <=> FALSE

Spec == Init /\ [][Next]_<< N >>

THEOREM Spec => []TRUE                        \* Due to subscript <<N>> in [][...]_<<N>>
============================================================================

---- CONFIG EmptyExistentialQuantifier ----
SPECIFICATION Spec
======
