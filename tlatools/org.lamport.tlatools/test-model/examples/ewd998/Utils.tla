------------------------------- MODULE Utils -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, Functions, SequencesExt

\* No support for RECURSIVE in PlusPy.
IsSimpleCycle(S, r) ==
  (* View r as a graph s.t. S is the graph's set of vertices and there 
     exists an edge from s to t iff f[s] = t. IsFiniteSet(DOMAIN r). *)
  LET 
   F[ i \in 1..Cardinality(S) ] == 
         IF i = 1 THEN << CHOOSE s \in S : TRUE >>
         ELSE LET seq == F[i-1]
                  head == Head(seq)
              IN << r[head] >> \o F[i-1]
  IN Range(F[Cardinality(S)]) = S

\* SimpleCycle is a recursive variant of the predicate IsSimpleCycle above. It
\* does not work with PlusPy, but is orders of magnitude faster when evaluated
\* by TLC.
SimpleCycle(S) ==
    LET sts == LET SE == INSTANCE SequencesExt IN SE!SetToSeq(S)
        RECURSIVE SimpleCycle(_,_,_)
        SimpleCycle(seq, prefix, i) ==
            IF i = Len(seq)
            THEN prefix @@ (seq[i] :> seq[1])
            ELSE SimpleCycle(seq, prefix @@ (seq[i] :> seq[i+1]), i+1)
    IN SimpleCycle(sts, sts[1] :> sts[2], 2)

=============================================================================
