---------------------- MODULE PrintTraceRace -------------------------
EXTENDS Naturals, Sequences
VARIABLES S

TestTypeInv == S \in [ q: Seq({1..2}),
                       i: 0..3]

TestInit == S = [q |->  << >>,
                 i |-> 1]

Send == /\ (S.i \leq 2)
        /\ (S' = [S EXCEPT !.i = (S.i + 1),!.q = Append(S.q,S.i)])

Done == /\ S.i > 2
        /\ UNCHANGED << S >>

TestNext == \/ Send
            \/ Done
============================================================