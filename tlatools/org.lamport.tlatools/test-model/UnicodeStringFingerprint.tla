---------------------- MODULE UnicodeStringFingerprint ----------------------
\* "é" is U+00E9 and "ǩ" is U+01E9. Their low bytes are equal.
VARIABLE s

Init == s \in {"é", "ǩ"}

Next == UNCHANGED s
=============================================================================
