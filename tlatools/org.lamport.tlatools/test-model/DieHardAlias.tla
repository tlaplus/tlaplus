---------------------------- MODULE DieHardAlias ----------------------------
EXTENDS DieHard

AliasSub ==
[
    \*bigBucket    |-> bigBucket,
    \*smallBucket  |-> smallBucket,
    \*action       |-> action,
    water_to_pour|-> water_to_pour
]
AliasSup ==
[
    bigBucket    |-> bigBucket,
    smallBucket  |-> smallBucket,
    action       |-> action,
    water_to_pour|-> water_to_pour,
    extraVar     |-> TLCGet("level")
]
=============================================================================
