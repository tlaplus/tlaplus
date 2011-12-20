----------------------- MODULE RemoveRedundantParens -----------------------
EXTENDS Integers, Sequences

CONSTANT TokId

Token == [type : {"left", "right", "other"}, id : TokId]

RECURSIVE ParenDepth(_, _)
ParenDepth(seq, i) == 
  IF i = 0 
    THEN 0
    ELSE CASE seq[i].type = "left"  -> ParenDepth(seq, i-1) + 1
           [] seq[i].type = "right" -> ParenDepth(seq, i-1) - 1
           [] seq[i].type = "other" -> ParenDepth(seq, i-1)

IsWellFormed(seq) == /\ \A i \in 1..Len(seq) : ParenDepth(seq, i) >= 0
                     /\ ParenDepth(seq, Len(seq)) = 0           
ExprOfMaxLen(n) == 
  UNION {{s \in [1..i -> Token] : IsWellFormed(s)} : i \in 0..n}


=============================================================================
\* Modification History
\* Last modified Mon Dec 19 17:36:43 PST 2011 by lamport
\* Created Mon Dec 19 17:20:10 PST 2011 by lamport
