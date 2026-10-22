------------------------- MODULE MongoReplBenchmark -------------------------
\* The model of general/performance/MongoRepl/MC.tla without the module stats,
\* which writes the statistics of the performance runs.
EXTENDS RaftMongo, TLC

CONSTANTS v1, s1, s2, s3

MCValue == {v1}

MCServer == {s1, s2, s3}

Symmetry == Permutations(MCServer)

Constraint ==
    /\ \A i \in Server : globalCurrentTerm <= 6
    /\ \A i \in Server : Len(log[i]) <= 15
=============================================================================
