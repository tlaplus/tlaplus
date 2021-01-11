------------------------------- MODULE Utils -------------------------------
EXTENDS Integers, Sequences, FiniteSets

\* This are mostly copy&pasted from various TLA+ community modules at:
\* https://github.com/tlaplus/CommunityModules/modules

Reduce(op(_,_), fun, from, to, base) == 
  (**************************************************************************)
  (* Reduce the elements in the range from..to of the function's co-domain. *)
  (**************************************************************************)
  LET reduced[i \in from..to] ==
          IF i = from THEN op(base, fun[i])
          ELSE op(reduced[i - 1], fun[i])
  IN reduced[to]

sum(a, b) ==
  a + b

Contains(s, e) ==
  (**************************************************************************)
  (* TRUE iff the element e \in ToSet(s).                                   *)
  (**************************************************************************)
  \E i \in 1..Len(s) : s[i] = e
  
RemoveAt(s, i) == 
  (**************************************************************************)
  (* Replaces the element at position i shortening the length of s by one.  *)
  (**************************************************************************)
  SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

Range(f) ==
  { f[x] : x \in DOMAIN f }

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

=============================================================================
