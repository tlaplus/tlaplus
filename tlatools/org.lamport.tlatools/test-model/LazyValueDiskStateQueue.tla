--------------------- MODULE LazyValueDiskStateQueue ---------------------
EXTENDS Naturals

N == 3

VARIABLES s, f, i, k

\* Neither the set nor the function is enumerable without first enumerating
\* SUBSET, which TLC defers. Thus, s is a SetPredValue and f a FcnLambdaValue.
Init == /\ s = {x \in SUBSET {0, 1, 2} : \A e \in x : e % 2 = 0}
        /\ f = [x \in SUBSET {0, 1} |-> x]
        /\ i = 0
        /\ k \in 1..64

Next == /\ i < N
        /\ i' = i + 1
        /\ UNCHANGED <<s, f, k>>

\* The view does not fingerprint s and f, which therefore remain lazy until
\* the DiskStateQueue writes them to disk.
View == <<i, k>>

\* Neither invariant converts s or f.
InvS == \A x \in s : \A e \in x : e % 2 = 0
InvF == \A x \in DOMAIN f : f[x] = x
=============================================================================
