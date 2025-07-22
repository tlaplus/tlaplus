---- MODULE ConstantContextTLCCache ----
EXTENDS Integers, TLC, TLCExt

COUNT_ID == 1

ASSUME TLCSet(COUNT_ID, 0)

inc(v) ==
    CASE TLCSet(COUNT_ID, TLCGet(COUNT_ID) + 1) -> v

defn == TLCCache(inc({ x : x \in 1 .. 5 }), {1})
derivedDefn == TLCCache(inc({ i \in 1 .. 5 : i + 1 \in defn }), {2})

VARIABLE x, y

ASSUME 5 \in defn
ASSUME 5 \notin derivedDefn

Init ==
    /\ y = defn
    /\ x = derivedDefn

Next ==
    /\ 1 \in defn
    /\ 1 \in derivedDefn
    /\ Assert(TLCGet(COUNT_ID) = 2, <<"count was", TLCGet(COUNT_ID)>>)
    /\ UNCHANGED <<x, y>>

====
