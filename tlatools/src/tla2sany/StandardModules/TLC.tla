------------------------------- MODULE TLC ----------------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
-----------------------------------------------------------------------------
Print(out, val) == val \* tlc2.module.TLC.Print(Value, Value)
PrintT(out) == TRUE    \* tlc2.module.TLC.PrintT(Value)
Assert(val, out) == IF val = TRUE THEN TRUE
                                  ELSE CHOOSE v : TRUE \* tlc2.module.TLC.Assert(Value, Value)
JavaTime == CHOOSE n : n \in Nat \* tlc2.module.TLC.JavaTime()
TLCGet(i) == CHOOSE n : TRUE \* tlc2.module.TLC.TLCGet(Value)
TLCSet(i, v) == TRUE \* tlc2.module.TLC.TLCSet(Value, Value)
-----------------------------------------------------------------------------
d :> e == [x \in {d} |-> e] \* tlc2.module.TLC.MakeFcn(Value, Value)
f @@ g == [x \in (DOMAIN f) \cup (DOMAIN g) |->
            IF x \in DOMAIN f THEN f[x] ELSE g[x]] \* tlc2.module.TLC.CombineFcn(Value, Value)
Permutations(S) == 
   {f \in [S -> S] : \A w \in S : \E v \in S : f[v]=w} \* tlc2.module.TLC.Permutations(Value)
-----------------------------------------------------------------------------
(***************************************************************************)
(* In the following definition, we use Op as the formal parameter rather   *)
(* than \prec because TLC Version 1 can't handle infix formal parameters.  *)
(***************************************************************************)
SortSeq(s, Op(_, _)) ==
    LET Perm == CHOOSE p \in Permutations(1 .. Len(s)) :
                  \A i, j \in 1..Len(s) : 
                     (i < j) => Op(s[p[i]], s[p[j]]) \/ (s[p[i]] = s[p[j]])
    IN  [i \in 1..Len(s) |-> s[Perm[i]]] \* tlc2.module.TLC.SortSeq(Value, Value)

RandomElement(s) == CHOOSE x \in s : TRUE \* tlc2.module.TLC.RandomElement(Value)

Any == CHOOSE x : TRUE \* tlc2.module.TLC.Any()

ToString(v) == (CHOOSE x \in [a : v, b : STRING] : TRUE).b \* tlc2.module.TLC.ToString(Value)

TLCEval(v) == v \* tlc2.module.TLC.TLCEval(Value)

=============================================================================
