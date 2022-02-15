---- MODULE MC ----
EXTENDS BloemenSCC, TLC, stats

SymmetryThreads == Permutations(Threads)

CartEdges == Nodes \X Nodes
=============================================================================
