----------------------------- MODULE TLAToPCal -----------------------------
EXTENDS Integers, Sequences, TLC


(***************************************************************************)
(* TP Mapping Specifiers                                                   *)
(***************************************************************************)
Location == [line : Nat, column : Nat]
  (*************************************************************************)
  (* This is a location in the file, which might be in the TLA+ spec or in *)
  (* the PCal code.                                                        *)
  (*************************************************************************)

loc1 <: loc2 == 
  (*************************************************************************)
  (* This is the "equals or to the left of" relation on locations.         *)
  (*************************************************************************)
  \/ loc1.line < loc2.line
  \/ /\ loc1.line = loc2.line
     /\ loc1.column =< loc2.column

Region == {r \in [begin : Location, end : Location] : r.begin <: r.end}
  (*************************************************************************)
  (* This describes a region within the file.  We say that region r1 is to *)
  (* the left of region r2 iff r1.end :< r2.begin                          *)
  (*************************************************************************)

(***************************************************************************)
(* TLA to PCal translation objects.                                        *)
(***************************************************************************)
TLAToken == [type : {"token"}, region  : Region]
  (*************************************************************************)
  (* This represents a region in the TLA+ spec.                            *)
  (*************************************************************************)
Paren    == [type : {"begin", "end"}, loc : Location]
  (*************************************************************************)
  (* This represents the beginning or end of a region in the PlusCal spec. *)
  (*************************************************************************)
Break    == [type : {"break"}, depth : Nat]
  (*************************************************************************
As explained below, this
   *************************************************************************)
TPObject == TLAToken \cup Paren \cup Break

RECURSIVE ParenDepth(_ , _)
ParenDepth(objSeq, pos) ==
  (*************************************************************************)
  (* Equals the parenthesis depth of the point in the TPObject sequence    *)
  (* objSeq just after element number pos, or at the beginning if pos = 0. *)
  (*************************************************************************)
  IF pos = 0 THEN 0
             ELSE LET obj == objSeq[pos]
                  IN  ParenDepth(objSeq, pos - 1) +
                        ( CASE obj.type = "begin" -> 1  []
                               obj.type = "end"   -> -1 []
                               OTHER              -> 0     )

(***************************************************************************)
(* WellFormed(seq) is true for a TPObject sequence iff it begins and ends  *)
(* with a parenthesis and all parentheses are properly matching.           *)
(***************************************************************************)
IsWellFormed(seq) ==  /\ seq # << >>
                      /\ seq[1].type = "begin"
                      /\ \A i \in 1..(Len(seq)-1) : ParenDepth(seq, i) >= 0
                      /\ ParenDepth(seq, Len(seq)) = 0

(***************************************************************************)
(* TokensInOrder(seq) is true for a TPObject sequence iff its TLAToken     *)
(* objects represent regions that are ordered properly--that is, if        *)
(* TLAToken T1 precedes TLAToken T2 in seq, then T1.region is to the left  *)
(* of T2.region.                                                           *)
(***************************************************************************)                      
TokensInOrder(seq) ==
  \A i \in 1..Len(seq) : 
     (seq[i].type = "token") => 
        \A j \in (i+1)..Len(seq) : 
           (seq[j].type = "token") =>
              (seq[i].region.end <: seq[j].region.begin)

MatchingParen(seq, pos) ==
  (*************************************************************************)
  (* If element number pos in TPObject sequence seq is a left paren, then  *)
  (* this equals the number n such that element number n is the matching   *)
  (* right paren.                                                          *)
  (*************************************************************************)
  CHOOSE i \in pos+1..Len(seq) :
     /\ ParenDepth(seq,i) = ParenDepth(seq, pos-1)
     /\ \A j \in (pos)..(i-1) : ParenDepth(seq, j) > ParenDepth(seq, pos-1)

(****************************************************************************
A TPSpec is a sequence of TPObject elements that has the following
interpretation.  The regions of the TLA+ spec contained within its
TLAToken elements contain the "important" text of the spec.  Text not
in those regions can be treated as if it were white space when
determining the PCal region that maps to a part of the TLA+ spec.

Each pair of matching parentheses defines the smallest syntactic unit
(e.g., expression or statement) whose translation contains the text in
the TLATokens between them.  All the top level (lowest depth)
parentheses between those matching parentheses describe successive
regions in the same part of the PCal text.  (Code in a macro and code
in a procedure is an example of two regions in completely different
parts of the PCal code, and hence are not successive regions.)  
Two successive regions are adjacent if, to higlight both of them, one
highlights those regions and the text between them.  If two successive
regions represented by two pairs of matching parentheses are not adjacent,
then the TPSpec contains a Break between them.  The depth of a break
indicates the number of parenthesis levels containing the break that represent 
PCal code in which the region between the parenthesized regions on either side of the
break should not be highlighted.

The following predicate asserts that seq is a proper TPSpec.
****************************************************************************)
IsTPSpec(seq) ==
   /\ IsWellFormed(seq)
   /\ TokensInOrder(seq)
   (************************************************************************)
   (* The following conjunct asserts that a Break comes between a right    *)
   (* and a left parenthesis.                                              *)
   (************************************************************************) 
   /\ \A i \in 1..Len(seq) :
         (seq[i].type = "break") => 
            /\ (1 < i) /\ (seq[i-1].type = "end")
            /\ (i < Len(seq)) /\ (seq[i+1].type = "begin")  
   (************************************************************************)
   (* The following conjunct asserts that matching parentheses have        *)
   (* non-decreasing locations, and that within a pair of matched          *)
   (* parentheses, the regions represented by the top-level matching       *)
   (* parentheses are properly ordered.                                    *)
   (************************************************************************)
   /\ \A i \in 1..Len(seq) :
         (seq[i].type = "begin") =>
            LET j  == MatchingParen(seq, i)
                dp == ParenDepth(seq, i-1) + 1
            IN  /\ PrintT(<<j, dp>>)
                /\ seq[i].loc <: seq[j].loc
                /\ \A k \in (i+1)..(j-1) :
                     /\ IF i = 1 THEN PrintT(<<"k", k>>) ELSE TRUE 
                     /\ seq[k].type = "end"
                     /\ IF i = 1 THEN PrintT(<<"k", k>>) ELSE TRUE 
                     /\ PrintT(ParenDepth(seq, k-1))
                     /\ ParenDepth(seq, k) = dp
                     /\ IF i = 1 THEN PrintT(<<"k", k>>) ELSE TRUE 
                     => \A m \in (k+1)..(j-1) :
                          /\ IF k = 4 THEN PrintT(<<"m", m>>) ELSE TRUE
                          /\ seq[m].type = "begin"
                          /\ ParenDepth(seq, m-1) = dp
                          => seq[k].loc <: seq[m].loc

TPSpec == {s \in Seq(TPObject) : IsTPSpec(s)}           
-----------------------------------------------------------------------------
(***************************************************************************)
(* The region in the PCal code specified by a Location in the TLA+ spec.   *)
(***************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* For Debugging                                                           *)
(*                                                                         *)
(* To simplify debugging, we assume that locations are all on the same     *)
(* line.                                                                   *)
(***************************************************************************)
Loc(pos) == [line |-> 0, column |-> pos]
Reg(beg, end) == [begin |-> Loc(beg), end |-> Loc(end)]
T(beg, end) == [type |->"token", region |-> Reg(beg, end)]
L(pos) == [type |-> "begin", loc |-> Loc(pos)]
R(pos) == [type |-> "end", loc |-> Loc(pos)]
B(dep) == [type |-> "break", depth |-> dep]

ObjSeq1 == << L(40), T(2,4), L(11),R(11), B(2), L(12), R(13), T(4, 9), R(42) >>

\*ObjSeq2 == << L(0), T(
=============================================================================
\* Modification History
\* Last modified Thu Dec 01 19:12:26 PST 2011 by lamport
\* Created Thu Dec 01 16:51:23 PST 2011 by lamport
