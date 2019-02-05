---- MODULE MC ----
EXTENDS BloemenSCC, TLC

SymmetryThreads == Permutations(Threads)

CartEdges == Nodes \X Nodes
=============================================================================
