\* Regression test for https://github.com/tlaplus/tlaplus/issues/1145
\*
\* The trailing [1] function application (OPCODE_fa) sets EvalControl.KeepLazy,
\* which propagates through F's body into the evaluation of the EXCEPT expression.
\* KeepLazy prevents OPCODE_fc from eagerly converting the FcnLambdaValue to
\* FcnRcdValue, so SubSeq receives a FcnLambdaValue whose toTuple()—before the
\* fix—ignores the EXCEPT and returns <<0,0,0,0>> instead of <<0,1,0,0>>.
\*
\* With the fix:    x = 1, Inv is violated  → TLC reports VIOLATION_SAFETY.
\* Without the fix: x = 0, Inv holds        → TLC reports SUCCESS (soundness bug).
---- MODULE Github1145b ----

EXTENDS Sequences, Naturals

F(seq) == SubSeq(seq, 2, 2)

VARIABLE x

Init == x = F([[i \in 1..4 |-> 0] EXCEPT ![2] = 1])[1]

Next == UNCHANGED x

Inv == x # 1

====
