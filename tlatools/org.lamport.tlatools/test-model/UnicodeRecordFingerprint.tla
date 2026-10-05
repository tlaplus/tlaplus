---------------------- MODULE UnicodeRecordFingerprint ----------------------
\* "é" is U+00E9 and "ǩ" is U+01E9. Their low bytes are equal.
\* SANY rejects é as an identifier, but @@ with a function over strings yields
\* the records [a |-> 1, é |-> 1] and [a |-> 1, ǩ |-> 1].
EXTENDS TLC

VARIABLE r

Init == r \in { [a |-> 1] @@ [x \in {"é"} |-> 1],
                [a |-> 1] @@ [x \in {"ǩ"} |-> 1] }

Next == UNCHANGED r
=============================================================================
