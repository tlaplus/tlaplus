------------------------------- MODULE Stones -------------------------------
(***************************************************************************)
(* The following problem was posed on an American radio program called Car *)
(* Talk.  Given a stone that weighs 40 pound and a balance scale, cut the  *)
(* stone into 4 pieces so that one can weigh any stone with an integral    *)
(* weight between 1 and 40 pounds.                                         *)
(*                                                                         *)
(* Since there are only 2^4 - 1 = 16 non-empty subsets of the 4 pieces, we *)
(* quickly deduce that we need to be able to put pieces on both sides of   *)
(* the balance to do this.  Putting a piece weighing w pounds on the same  *)
(* side of the balance as the stone we are weighing is equivalent to       *)
(* placing a stone weighing -w pounds on the opposite side, we quickly see *)
(* that the problem is to find natural numbers w1, ...  , w4 such that for *)
(* every weight w in 1..40, there exist numbers x1, ...  , x4 in {-1,0,1}  *)
(* such that w = x1*w1 + ...  + x4*w4.                                     *)
(*                                                                         *)
(* It's easy to have TLC find the solution by having it evaluate an        *)
(* assumption that's a formula that quantifies the subformula              *)
(*                                                                         *)
(*    IF \A w \in 1..40 : w = x1*w1 + ... + x4*w4                          *)
(*      THEN PrintT(<<w1, ... , w4>>)                                      *)
(*      ELSE FALSE                                                         *)
(*                                                                         *)
(* over x1, ...  , x4 and w1, ..., w4.  As a more interesting problem, we  *)
(* here do it replacing 40 and 4 by constants W and N.                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

(***************************************************************************)
(* We will need to take sums of sequences of numbers, so we define SeqSum  *)
(* to do that.                                                             *)
(***************************************************************************)
RECURSIVE SeqSum(_)
SeqSum(s) == IF Len(s) = 0 THEN 0 ELSE Head(s) + SeqSum(Tail(s))

CONSTANTS W, N
ASSUME W \in Nat /\ N \in 1..W

(***************************************************************************)
(* Let a partition be a sequence N numbers that sum to W.  To find a       *)
(* solution, we let TLC examine all such partitions.  For efficiency, we   *)
(* don't have it check partitions that are the same except for the order   *)
(* of the numbers.  So, we have it check only ordered partitions, which    *)
(* are non-decreasing sequences of natural numbers.                        *)
(*                                                                         *)
(* We define the recursive operator Partitions so that for seq an ordered  *)
(* sequence of numbers that sum to W - wt, Partitions(seq, wt) is the set  *)
(* of all ordered partitions that end in the subsequence seq.  Thus,       *)
(* Partitions(<< >>, W) is the set of all ordered partitions.              *)
(*                                                                         *)
(* Since the first N - Len(seq) elements of a such an ordered partition    *)
(* must all be at least 1 and at most Head(s), we see that Partitions(seq, *)
(* wt) is non-empty only if                                                *)
(*                                                                         *)
(*    N - Len(seq) =< wt =< Head(seq) * (N - Len(seq))                     *)
(*                                                                         *)
(* This observation explains the local definition of S in the following    *)
(* definition.                                                             *)
(***************************************************************************)
RECURSIVE Partitions(_ , _)
Partitions(seq, wt) ==
  IF Len(seq) = N
    THEN {seq}
    ELSE LET r == N - Len(seq)
             max == IF Len(seq) = 0 THEN wt ELSE Head(seq)
             S == {x \in 1..max : /\ (r-1) =< (wt - x)
                                  /\ wt =< x*r          }
         IN UNION { Partitions(<<x>> \o seq, wt - x ) : x \in S }

(***************************************************************************)
(* For convenience, we define Weighs(seq, wt) to be true if the elements   *)
(* of the sequence seq sum to wt.                                          *)
(***************************************************************************)
Weighs(seq, wt) == 
  \E coef \in [1..N -> -1..1] : 
      SeqSum([i \in 1..N |-> coef[i] * seq[i]]) = wt

(***************************************************************************)
(* We now assert the following ASSUME, which TLC will evaluate by either   *)
(* printing a solution to the problem or printing "No solution".  We then  *)
(* just create a model that assigns values to W and N and run TLC.         *)
(***************************************************************************)
ASSUME \/ \E p \in Partitions(<< >>, W) :
              IF \A wt \in 1..W : Weighs(p, wt) 
                THEN PrintT(p) 
                ELSE FALSE
       \/ PrintT("No solution")

(***************************************************************************)
(* It takes TLC just a few seconds to find the solution to the original    *)
(* problem, with W = 40 and N = 4.  That solution should allow you to      *)
(* guess for what values of W and N there exists a solution and what the   *)
(* solution is.  Proving correctness of your guess is harder.              *)
(*                                                                         *)
(* TLC will check the assumption in less than a minute You can quickly     *)
(* check your guess with values of W and N up to around 70 and 6,          *)
(* respectively.  However, it will probably run for centuries with W large *)
(* enough so there is no solution for N = 5.  I doubt if there's any way   *)
(* to do much better with a brute force solution.                          *)
(***************************************************************************)
=============================================================================
\* Modification History
\* Last modified Wed Feb 04 16:44:37 PST 2015 by lamport
\* Created Wed Feb 04 13:33:09 PST 2015 by lamport
