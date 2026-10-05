--------------------- MODULE UnicodeFunctionFingerprint ---------------------
\* "é" is U+00E9 and "ǩ" is U+01E9. Their low bytes are equal.
VARIABLE f

Init == f \in { [x \in {"é"} |-> 1], [x \in {"ǩ"} |-> 1] }

Next == UNCHANGED f
=============================================================================
