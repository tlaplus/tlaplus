------------------------------- MODULE Peano -------------------------------
PeanoAxioms(N, Z, Sc) == 
  /\ Z \in N
  /\ Sc \in [N -> N]
  /\ \A n \in N : (\E m \in N : n = Sc[m]) <=> (n # Z)
  /\ \A S \in SUBSET N : (Z \in S) /\ (\A n \in S : Sc[n] \in S) => (S = N)

ASSUME \E N, Z, Sc : PeanoAxioms(N, Z, Sc)

Succ == CHOOSE Sc : \E N, Z : PeanoAxioms(N, Z, Sc)
Nat  == DOMAIN Succ
Zero == CHOOSE Z : PeanoAxioms(Nat, Z, Succ)
=============================================================================
