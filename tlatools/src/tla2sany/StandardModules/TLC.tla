------------------------------- MODULE TLC ----------------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
-----------------------------------------------------------------------------
Print(out, val) == val
PrintT(out) == TRUE
Assert(val, out) == IF val = TRUE THEN TRUE
                                  ELSE CHOOSE v : TRUE
JavaTime == CHOOSE n : n \in Nat
TLCGet(i) == CHOOSE n : TRUE
TLCSet(i, v) == TRUE
-----------------------------------------------------------------------------
d :> e == [x \in {d} |-> e]
f @@ g == [x \in (DOMAIN f) \cup (DOMAIN g) |->
            IF x \in DOMAIN f THEN f[x] ELSE g[x]]
Permutations(S) == 
   {f \in [S -> S] : \A w \in S : \E v \in S : f[v]=w}
-----------------------------------------------------------------------------
(***************************************************************************)
(* In the following definition, we use Op as the formal parameter rather   *)
(* than \prec because TLC Version 1 can't handle infix formal parameters.  *)
(***************************************************************************)
SortSeq(s, Op(_, _)) ==
    LET Perm == CHOOSE p \in Permutations(1 .. Len(s)) :
                  \A i, j \in 1..Len(s) : 
                     (i < j) => Op(s[p[i]], s[p[j]]) \/ (s[p[i]] = s[p[j]])
    IN  [i \in 1..Len(s) |-> s[Perm[i]]]

RandomElement(s) == CHOOSE x \in s : TRUE

Any == CHOOSE x : TRUE

ToString(v) == (CHOOSE x \in [a : v, b : STRING] : TRUE).b

TLCEval(v) == v
=============================================================================
