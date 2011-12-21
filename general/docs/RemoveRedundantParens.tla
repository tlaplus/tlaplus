----------------------- MODULE RemoveRedundantParens -----------------------
(***************************************************************************)
(* Let an expression be a sequence of tokens, some of which are left and   *)
(* right parenthesis tokens, in which parentheses are balanced.  The goal  *)
(* is an algorithm that removes redundant parentheses from the expression. *)
(* A pair of matching left and right parentheses (a( and )b) are redundant *)
(* if they occur immediately inside another pair of matching parentheses,  *)
(* as in                                                                   *)
(*                                                                         *)
(*   (p( (a( xxx (u( xxx )v) xxx )b) )q)                                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC

(***************************************************************************)
(* A Token has a type, which is "left", "right", or "other" and an id,     *)
(* which is an element of the set TokId                                    *)
(***************************************************************************)
CONSTANT TokId
Token == [type : {"left", "right", "other"}, id : TokId]
----------------------------------------------------------------------------
(***************************************************************************)
(* We now define Result(seq) to be the output that the algorithm is        *)
(* supposed to produce.  It's defined recursively to keep removing         *)
(* matching redundant parentheses until there are no left.  We make some   *)
(* preliminary definitions, some of which are used in the algorithm as     *)
(* well.                                                                   *)
(***************************************************************************)

(***************************************************************************)
(* ParenDepth(seq, i) is the parenthesis depth in the expression seq just  *)
(* after the i-th token in seq, where ParenDepth(seq, 0) = 0.              *)
(***************************************************************************)
RECURSIVE ParenDepth(_, _)
ParenDepth(seq, i) == 
  IF i = 0 
    THEN 0  
    ELSE CASE seq[i].type = "left"  -> ParenDepth(seq, i-1) + 1
           [] seq[i].type = "right" -> ParenDepth(seq, i-1) - 1
           [] seq[i].type = "other" -> ParenDepth(seq, i-1)

(***************************************************************************)
(* IsWellFormed(seq) is true iff all parentheses in seq are properly       *)
(* matched.                                                                *)
(***************************************************************************)
IsWellFormed(seq) == /\ \A i \in 1..Len(seq) : ParenDepth(seq, i) >= 0
                     /\ ParenDepth(seq, Len(seq)) = 0
                                
(***************************************************************************)
(* For m < n, this is true iff the m-th and n-th elements of seq are       *)
(* matching parentheses.                                                   *)
(***************************************************************************)
AreMatching(seq, m, n) == /\ seq[m].type = "left"
                          /\ seq[n].type = "right"
                          /\ LET sseq == SubSeq(seq, m, n)
                             IN  /\ ParenDepth(sseq, n-m+1) = 0
                                 /\ \A i \in 1..(n-m) :
                                       ParenDepth(sseq, i) > 0

(***************************************************************************)
(* We now define some useful operators on sequences.                       *)
(***************************************************************************)
RemoveElement(seq, i) == 
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]

Last(seq) == seq[Len(seq)]

RemoveLast(seq) == RemoveElement(seq, Len(seq))
                  
RECURSIVE Result(_)
Result(seq) ==
  IF \E r \in (2..(Len(seq)-2)) \X (3..(Len(seq)-1)) : 
       /\ r[1] < r[2]
       /\ AreMatching(seq, r[1], r[2])
       /\ AreMatching(seq, r[1]-1, r[2]+1)
    THEN LET r == 
              CHOOSE r \in (2..(Len(seq)-2)) \X (3..(Len(seq)-1)) : 
               /\ r[1] < r[2]
               /\ AreMatching(seq, r[1], r[2])
               /\ AreMatching(seq, r[1]-1, r[2]+1)
         IN Result(RemoveElement(RemoveElement(seq, r[2]), r[1]))
    ELSE seq
----------------------------------------------------------------------------
(***************************************************************************)
(* The following are some operators useful for writing and debugging the   *)
(* algorithm.  ExprOfMaxLen(n) is the set of all expressions of length at  *)
(* most n.  The algorithm has been checked for all expressions in          *)
(* ExprOfMaxLen(9).  For ExprOfMaxLen(10), there are too many initial      *)
(* states.                                                                 *)
(***************************************************************************)
ExprOfMaxLen(n) == 
  UNION {{s \in [1..i -> Token] : IsWellFormed(s)} : i \in 0..n}

(***************************************************************************)
(* Pr(seq) is a value that, when printed, provides a compact               *)
(* representation of the expression seq.                                   *)
(***************************************************************************)
PrT(tok) == CASE tok.type = "left" -> <<"(", tok.id>> []
                 tok.type = "right" -> <<tok.id, ")">> []
                 tok.type = "other" -> tok.id
     
Pr(seq) == [i \in 1..Len(seq) |-> PrT(seq[i])]            

(***************************************************************************)
(* Some operators for writing expressions compactly.                       *)
(***************************************************************************)
L(i) == [type |-> "left", id |-> i]
R(i) == [type |-> "right", id |-> i]
O(i) == [type |-> "other", id |-> i]
----------------------------------------------------------------------------
(****************************************************************************

--algorithm Remove {
  variables 
    in \in ExprOfMaxLen(9), 
             \* The input.  
     
    out = << >>,           \* The output
    unmatchedLeft = << >>, \* Sequence of indices in `out' of unmatched "("s in out
    lastMatchedLeft = -1,  \* Index in `out' of "(" matched by last ")" in `out'.
                           \* A value of -1 means there is none.
    lastAddedRight = -1,   \* Index in `in' of last ")"  added to `out'.
                           \* A value of -1 means there is none.
    i = 1,                 \* Next element of `in' to examine.
            
 { while (i =< Len(in)) {
      if (in[i].type = "left") {
        unmatchedLeft := Append(unmatchedLeft, Len(out)+1)
      }
      else if (in[i].type = "right") {
        if ( /\ i = lastAddedRight + 1
             /\ lastMatchedLeft = unmatchedLeft[Len(unmatchedLeft)]+1 ) {
          out := RemoveLast(RemoveElement(out, lastMatchedLeft));
        };
        lastMatchedLeft := Last(unmatchedLeft);
        unmatchedLeft := RemoveLast(unmatchedLeft);
        lastAddedRight := i
      } ;
      out := Append(out, in[i]);
      i := i+1;
    };
    \* If out is not the correct result, print in, out and the
    \* correct result and report an error.
    if ( out # Result(in)) {
       print <<"in:", Pr(in)>>;
       print <<"out;", Pr(out)>>;
       print <<"res:",Pr(Result(in))>>;
       assert FALSE
    } 
 }

}
****************************************************************************)
\* BEGIN TRANSLATION
VARIABLES in, out, unmatchedLeft, lastMatchedLeft, lastAddedRight, i, pc

vars == << in, out, unmatchedLeft, lastMatchedLeft, lastAddedRight, i, pc >>

Init == (* Global variables *)
        /\ in \in ExprOfMaxLen(10)
        /\ out = << >>
        /\ unmatchedLeft = << >>
        /\ lastMatchedLeft = -1
        /\ lastAddedRight = -1
        /\ i = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i =< Len(in)
               THEN /\ IF in[i].type = "left"
                          THEN /\ unmatchedLeft' = Append(unmatchedLeft, Len(out)+1)
                               /\ UNCHANGED << out, lastMatchedLeft, 
                                               lastAddedRight >>
                          ELSE /\ IF in[i].type = "right"
                                     THEN /\ IF /\ i = lastAddedRight + 1
                                                /\ lastMatchedLeft = unmatchedLeft[Len(unmatchedLeft)]+1
                                                THEN /\ out' = RemoveLast(RemoveElement(out, lastMatchedLeft))
                                                ELSE /\ TRUE
                                                     /\ out' = out
                                          /\ lastMatchedLeft' = Last(unmatchedLeft)
                                          /\ unmatchedLeft' = RemoveLast(unmatchedLeft)
                                          /\ lastAddedRight' = i
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << out, unmatchedLeft, 
                                                          lastMatchedLeft, 
                                                          lastAddedRight >>
                    /\ pc' = "Lbl_2"
               ELSE /\ IF out # Result(in)
                          THEN /\ PrintT(<<"in:", Pr(in)>>)
                               /\ PrintT(<<"out;", Pr(out)>>)
                               /\ PrintT(<<"res:",Pr(Result(in))>>)
                               /\ Assert(FALSE, 
                                         "Failure of assertion at line 136, column 8.")
                          ELSE /\ TRUE
                    /\ pc' = "Done"
                    /\ UNCHANGED << out, unmatchedLeft, lastMatchedLeft, 
                                    lastAddedRight >>
         /\ UNCHANGED << in, i >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ out' = Append(out, in[i])
         /\ i' = i+1
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << in, unmatchedLeft, lastMatchedLeft, lastAddedRight >>

Next == Lbl_1 \/ Lbl_2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Dec 20 15:29:06 PST 2011 by lamport
\* Created Mon Dec 19 17:20:10 PST 2011 by lamport
