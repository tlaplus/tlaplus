-------------------------------- MODULE Grid5k --------------------------------
\* This spec executes
\*  variable x = [i \in 1..N |-> 0];
\*  while (TRUE) {
\*    with (i \in 1..N) {
\*        x[i] := (x[i] + 1) % K ;
\*        \* SUBSET 1..L causes TLC to generate the power set of the set 1..L.
\*        \* For each set in the power set, TLC evaluates if the set's 
\*        \* cardinality is L... KaBOOM!
\*        await \E s \in SUBSET (1..L): Cardinality(s) = L
\*        }
\*   }
\*  Thus,  - N is the number of states computed for each evaluation of the
\*           next-state action
\*         - K^N is the total number of distinct states
\*         - The time to compute a single state is asymptotically
\*           proportional to 2^L.
\*         - C defines the number of initial states. Let C=n
\*           then the state graph has n isomorphic disjunct subgraphs.
EXTENDS Integers, FiniteSets

CONSTANTS N, K, L, C
VARIABLE x, y

\* To trigger FcnRcdValue#createTable domain must not be int range
Dom == 0..1 \union 2..N

Init == /\ x = [i \in Dom |-> 0]
        /\ y \in 1..C

Next == /\ UNCHANGED y
        /\ \E i \in Dom : /\ x' = [x EXCEPT ![i] = (@ + 1) % K]
        /\ \E s \in SUBSET (1..L): Cardinality(s) = L

Inv ==
    \A i \in Dom : x[i] < K
=============================================================================
