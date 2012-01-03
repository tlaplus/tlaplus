-------------------------------- MODULE Grid5k -------------------------------
\* This spec executes
\*  variable x = [i \in 1..N |-> 0];
\*  while (TRUE) {
\*    with (i \in 1..N) {
\*        x[i] := (x[i] + 1) % K ;
\*        await SUBSET 1..L \subseteq SUBSET 1..L
\*        }
\*   }
\*  Thus,  - N is the number of states computed for each evaluation of the
\*           next-state action
\*         - K^N is the total number of distinct states
\*         - The time to compute a single state is asymptotically
\*           proportional to 2^L
EXTENDS Integers, FiniteSets

CONSTANTS N, K, L
VARIABLE x

Init == x = [i \in 1..N |-> 0]

Next ==
  \E i \in 1..N : /\ x' = [x EXCEPT ![i] = (@ + 1) % K]
                  /\ SUBSET (1..L) \subseteq SUBSET (1..L)

=============================================================================

