------------------------------ MODULE _Possible ------------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

ASSUME TLCSet("s:_possible", <<>>)

LOCAL _Update(Op(_,_), val) ==
    TLCSet("s:_possible", Op(TLCGet("s:_possible"), val))

_Track(expr, name) ==
    _Update(LAMBDA old, b:
        IF b
        THEN
            IF name \in DOMAIN old
            THEN [old EXCEPT ![name] = @ + 1]
            ELSE old @@ (name :> 1)
        ELSE old @@ (name :> 0), expr)

LOCAL _Merge(a, b) ==
    [name \in (DOMAIN a) \cup (DOMAIN b) |->
        (IF name \in DOMAIN a THEN a[name] ELSE 0) +
        (IF name \in DOMAIN b THEN b[name] ELSE 0)]

_Counts == \* Java override for efficiency
    LET workers == TLCGet("all:named")["s:_possible"]
        n == Len(workers)
        Fold[i \in 0..n] ==
            IF i = 0 THEN <<>>
            ELSE _Merge(Fold[i-1], workers[i])
    IN Fold[n]

_Check ==
    LET counts == _Counts
    IN (\E name \in DOMAIN counts : counts[name] = 0)
       => (PrintT(counts) /\ FALSE)

_CheckName(name) ==
    LET counts == _Counts
    IN (name \notin DOMAIN counts \/ counts[name] = 0)
       => (PrintT(counts) /\ FALSE)

_PrintCounts == PrintT(_Counts)

=============================================================================
