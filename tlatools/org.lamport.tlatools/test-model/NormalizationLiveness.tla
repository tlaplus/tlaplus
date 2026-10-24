------------------------ MODULE NormalizationLiveness ------------------------
\* TLC normalizes a set enumeration only when it has to (see
\* NormalizationAssume.tla). Binding a set enumeration in a liveness property
\* doesn't have to, so TLC checks Live even though it cannot compare the
\* elements 1 and "a". Live is the temporal counterpart of
\* NormalizationCases!MixedBoundMember.
VARIABLE x

Spec == x = FALSE /\ [][x' = ~x]_x

\* Liveness#astToLive binds S when it constructs the tableau of Live.
Live == \A S \in {{1, "a"}} : <>(1 \in S)
=============================================================================
