--------------------- MODULE FingerprintExceptionNextCallstack ------------------ 

EXTENDS Integers

VARIABLE x

Op(S) == LET iter[s \in SUBSET S] == s IN iter[S]
Init == x = 0
Next == x' = Op(42)
Spec == Init /\ [][Next]_x

=============================================================================

   \* Simulates e.g. user passing 42 instead of DOMAIN <<1,2>>.
   MapThenFoldSet(+, 0, LAMBDA i: <<1,2>>[i], LAMBDA S: Min(S), 42)
