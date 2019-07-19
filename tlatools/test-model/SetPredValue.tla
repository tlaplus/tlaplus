---- MODULE SetPredValue ----
EXTENDS TLC, FiniteSets, Integers

Range(F) == { F[x] : x \in DOMAIN F }
Min(n, m) == IF n < m THEN n ELSE m

LP(S, T, p) == LET ss == { s \in SUBSET S : Cardinality(s) = p}
                          IN { e \in [ T -> ss ] : 
                                Cardinality(Range(e)) = Min(Cardinality(T), Cardinality(ss)) }

ASSUME PrintT(LP(1..4, {"a","b","c"}, 2))

=============================
