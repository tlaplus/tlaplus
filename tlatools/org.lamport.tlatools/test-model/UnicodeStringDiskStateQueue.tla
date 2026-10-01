-------------------- MODULE UnicodeStringDiskStateQueue --------------------
\* https://github.com/tlaplus/tlaplus/issues/1076
EXTENDS Naturals, TLC

N == 10

VARIABLES s, i

Init == /\ s \in {"cafe", "café"}
        /\ i = 0

Next == /\ i < N
        /\ i' = i + 1
        /\ UNCHANGED s

\* s = "café" compares the tokens of the strings, and the tokens survive the
\* round trip through the disk state queue. ToString(s) compares the text of
\* the strings, and the text does not survive it.
Inv == ToString(s) \in {ToString("cafe"), ToString("café")}
=============================================================================
