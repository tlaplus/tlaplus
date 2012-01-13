----------------------------- MODULE TLAToPCal -----------------------------
EXTENDS Integers, Sequences, TLC

(***************************************************************************)
(* We define the minimum and maximum of a nonempty set of numbers, and the *)
(* absolute value of a number.                                             *)
(***************************************************************************)
Min(S) == CHOOSE i \in S : \A j \in S : i =< j
Max(S) == CHOOSE i \in S : \A j \in S : i >= j
Abs(x) == Max({x, -x})

(***************************************************************************)
(* TP Mapping Specifiers               .                                   *)
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

(***************************************************************************)
(* We define Dist(loc1, loc2) to be a natural number representing a        *)
(* distance between locations loc1 and loc2.  This distance is used only   *)
(* to determine which of two other locations a location is closer to.      *)
(* Thus, its magnitude doesn't matter.  I should make Dist a parameter of  *)
(* the spec, but it's less effort to give it some reasonable definition.   *)
(***************************************************************************)
Dist(loc1, loc2) == 
   10000 * Abs(loc2.line - loc1.line) + Abs(loc2.column - loc1.column)
   
Region == {r \in [begin : Location, end : Location] : r.begin <: r.end}
  (*************************************************************************)
  (* This describes a region within the file.  We say that region r1 is to *)
  (* the left of region r2 iff r1.end :< r2.begin                          *)
  (*************************************************************************)

(***************************************************************************)
(* TLA to PCal translation objects.                                        *)
(***************************************************************************)
TLAToken == [type : {"token"}, region  : Region, inExpr : BOOLEAN]
  (*************************************************************************)
  (* This represents a region of tokens in the TLA+ spec, with inExpr      *)
  (* being true iff that region lies within an expression.                 *)
  (*************************************************************************)
Paren    == [type : {"begin", "end"}, loc : Location]
  (*************************************************************************)
  (* This represents the beginning or end of a region in the PlusCal spec. *)
  (*************************************************************************)
Break    == [type : {"break"}, depth : Nat]
  (*************************************************************************)
  (* A Break comes between a right and left Paren at the same parenthesis  *)
  (* level (possibly with TLATokens also between them).  It indicates that *)
  (* there is some PlusCal code between the locations indicated by those   *)
  (* parentheses that should not be displayed when displaying the PlusCal  *)
  (* code for parenthesis levels between the current level lv and lv -     *)
  (* depth.                                                                *)
  (*************************************************************************)
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
TokensOf(seq) == {i \in 1..Len(seq) : seq[i].type = "token"}

TokensInOrder(seq) ==
  \A i \in TokensOf(seq) : 
     \A j \in { jj \in TokensOf(seq) : jj > i} : 
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

(***************************************************************************)
(* A TPMap is a sequence of TPObject elements that has the following       *)
(* interpretation.  The regions of the TLA+ spec contained within its      *)
(* TLAToken elements contain the "important" text of the spec.  Text not   *)
(* in those regions can be treated as if it were white space when          *)
(* determining the PCal region that maps to a part of the TLA+ spec.       *)
(*                                                                         *)
(* Each pair of matching parentheses defines the smallest syntactic unit   *)
(* (e.g., expression or statement) whose translation contains the text in  *)
(* the TLATokens between them.  All the top level (lowest depth)           *)
(* parentheses between those matching parentheses describe successive      *)
(* regions in the same part of the PCal text.  (Code in a macro and code   *)
(* in a procedure is an example of two regions in completely different     *)
(* parts of the PCal code, and hence are not successive regions.) Two      *)
(* successive regions are adjacent if, to higlight both of them, one       *)
(* highlights those regions and the text between them.  If two successive  *)
(* regions represented by two pairs of matching parentheses are not        *)
(* adjacent, then the TPMap contains a Break between them.  The depth of a *)
(* break indicates the number of parenthesis levels containing the break   *)
(* that represent PCal code in which the region between the parenthesized  *)
(* regions on either side of the break should not be highlighted.          *)
(*                                                                         *)
(* The following predicate asserts that seq is a proper TPMap.             *)
(***************************************************************************)
IsTPMap(seq) ==
   (************************************************************************)
   (* There is at least one TLAToken between every matching pair of        *)
   (* parentheses.                                                         *)
   (************************************************************************)
   /\ \A i \in 1..Len(seq) :
         (seq[i].type = "begin") =>
            \E j \in (i+1)..(MatchingParen(seq,i)-1) : seq[j].type = "token"
   (************************************************************************)
   (* A token in an expression is surrounded by parentheses.               *)
   (************************************************************************)
   /\ \A i \in TokensOf(seq) : seq[i].inExpr =>  /\ seq[i-1].type = "begin"
                                                 /\ seq[i+1].type = "end"
   /\ IsWellFormed(seq)
   /\ TokensInOrder(seq)
   (************************************************************************)
   (* The following conjunct asserts that a Break comes between a right    *)
   (* and a left parenthesis at its level, perhaps with intervening        *)
   (* tokens.                                                              *)
   (************************************************************************) 
   /\ \A i \in 1..Len(seq) :
         (seq[i].type = "break") => 
            /\ \E j \in 1..(i-1) : 
                  /\ seq[j].type = "end"
                  /\ \A k \in (j+1)..(i-1) : seq[j].type # "begin"
            /\  \E j \in (i+1)..Len(seq) : 
                  /\ seq[j].type = "begin"
                  /\ \A k \in (i+1)..(j-1) : seq[j].type # "end"
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
            IN  /\ seq[i].loc <: seq[j].loc
                /\ \A k \in (i+1)..(j-1) :
                     /\ seq[k].type = "end"
                     /\ ParenDepth(seq, k) = dp
                     => \A m \in (k+1)..(j-1) :
                          /\ seq[m].type = "begin"
                          /\ ParenDepth(seq, m-1) = dp
                          => seq[k].loc <: seq[m].loc

TPMap == {s \in Seq(TPObject) : IsTPMap(s)}           
-----------------------------------------------------------------------------
(***************************************************************************)
(* The Region in the PCal code specified by a Region in the TLA+ spec.     *)
(***************************************************************************)

RegionToTokPair(spec, reg) ==
  (*************************************************************************)
  (* A pair of integers that are the positions of the pair of TLATokens in *)
  (* spec such that they and the TLATokens between them are the ones that  *)
  (* the user has chosen if she has highlighted the region specified by    *)
  (* reg.  (Both tokens could be the same.)                                *)
  (*                                                                       *)
  (* If the region reg does not intersect with the region of any TLAToken  *)
  (* (so it lies entirely inside "white space"), then the value is <<t,    *)
  (* t>> for the token t that lies either to the left or the right of reg. *)
  (*************************************************************************)
  LET TokensContaining(loc) == 
         (******************************************************************)
         (* The set of positions of tokens in spec containing loc.  (It    *)
         (* contains 0 or 1 element.)                                      *)
         (******************************************************************)
         {i \in TokensOf(spec) : /\ spec[i].region.begin <: loc
                                 /\ spec[i].region.begin # loc
                                 /\ loc <: spec[i].region.end
                                 /\ loc # spec[i].region.end  }
                          
      TokensToLeft(loc) == 
        (*******************************************************************)
        (* The set of positions of tokens in spec at or to the left of     *)
        (* loc.                                                            *)
        (*******************************************************************)
        {i \in TokensOf(spec) : spec[i].region.end <: loc}

      TokensToRight(loc) ==
        (*******************************************************************)
        (* The set of positions of tokens in spec at or to the right of    *)
        (* loc.                                                            *)
        (*******************************************************************)
        {i \in TokensOf(spec) : loc <: spec[i].region.begin}

      TokensInRegion == 
        (*******************************************************************)
        (* The set of tokens whose regions lie within reg.                 *)
        (*******************************************************************)
        TokensToRight(reg.begin) \cap TokensToLeft(reg.end)

      S == TokensInRegion \cup TokensContaining(reg.begin) 
            \cup TokensContaining(reg.end)
      
  IN  IF S # {}
        THEN <<Min(S), Max(S)>>
        ELSE LET LeftOfReg  == TokensToLeft(reg.begin)
                 LeftTok == Max(LeftOfReg)
                 RightOfReg == TokensToRight(reg.end)
                 RightTok == Min(RightOfReg)
             IN  CASE LeftOfReg = {}  -> <<RightTok, RightTok>> []
                      RightOfReg = {} -> <<LeftTok, LeftTok>>   []
                      OTHER ->
                        LET dl == Dist(spec[LeftTok].region.end, reg.begin)
                            dr == Dist(spec[RightTok].region.begin, reg.end)
                        IN  CASE dl < dr -> <<LeftTok, LeftTok>>   []
                                 dl > dr -> <<RightTok, RightTok>> []
                                 dl = dr -> <<LeftTok, RightTok>>
               
TokPairToParens(spec, ltok, rtok) ==
  (*************************************************************************)
  (* Assumes ltok and rtok are the positions of TLAToken elements of the   *)
  (* TPMap spec with ltok equal to or to the left of rtok.  It equals the  *)
  (* pair <<lparen, rparen>> where lparen is the position of the           *)
  (* right-most left paren to the left of ltok that enters level dp and    *)
  (* rparen is the position of the left-most right paren to the right of   *)
  (* rtok that leaves level dp, where dp is defined as follows:            *)
  (*                                                                       *)
  (* Let d be the minimum paren depth any token from ltok and rtok.  If    *)
  (* ltok # rtok and every TLAToken element from positions ltok through    *)
  (* rtok is an expression token, then dp = d+1.  Otherwise, dp = d.       *)
  (*************************************************************************)
  LET d == Min ( {ParenDepth(spec, i) : i \in ltok..rtok} )
      dp == IF /\ ltok # rtok 
               /\ \A i \in ltok..rtok : (spec[i].type = "token") =>
                                          spec[i].inExpr 
              THEN d + 1
              ELSE d
      lp == Max ( {i \in 1..ltok : /\ spec[i].type = "begin"
                                   /\ ParenDepth(spec,i) = dp} )
      rp == Min ( {i \in rtok..Len(spec) : /\ spec[i].type = "end"
                                           /\ ParenDepth(spec,i-1) = dp} )
  IN  <<lp, rp>>
-----------------------------------------------------------------------------
(***************************************************************************)
(* For Debugging                                                           *)
(*                                                                         *)
(* To simplify debugging, we assume that locations are all on the same     *)
(* line.                                                                   *)
(***************************************************************************)
Loc(pos) == [line |-> 0, column |-> pos]
Reg(beg, end) == [begin |-> Loc(beg), end |-> Loc(end)]
T(beg, end) == [type |->"token", region |-> Reg(beg, end), inExpr |-> FALSE]
TE(beg, end) == [type |->"token", region |-> Reg(beg, end), inExpr |-> TRUE]
L(pos) == [type |-> "begin", loc |-> Loc(pos)]
R(pos) == [type |-> "end", loc |-> Loc(pos)]
B(dep) == [type |-> "break", depth |-> dep]

tpMap_1 == << L(-5), T(2,3), L(11), T(3, 4), L(12), T(4,5), R(13), 
              T(6,7), R(14), T(8, 9), R(42) >>
tpRegion_1 == Reg(5,20)      
              
tpMap_2 == <<L(10), T(1,2), L(11), T(3,4), L(12), T(5,6), L(13), T(7,8), R(14),
             (* 10 *)T(9,10),  R(15), B(1), L(16), T(11,12), L(17), T(13,14), R(18), 
             (* 18 *) R(19), T(15,16), R(20), R(21)>>
             
tpRegion1 == Reg(0,16)

tpMap1 == << L(1), L(2), TE(1,2), R(3), L(4), TE(2,3), 
             R(5), T(4, 5), L(6), TE(5,6), R(7), R(8)>>

SpecToRegions(spec) ==
  (*************************************************************************)
  (* The set of all regions whose endpoints are in the smallest region     *)
  (* containing all the tokens of spec.                                    *)
  (*************************************************************************)
  LET TT == TokensOf(spec)
      left == Min({spec[i].region.begin.column : i \in TT})
      right == Max({spec[i].region.end.column : i \in TT})
  IN  { Reg(r[1], r[2]) : 
          r \in {rr \in (left..right) \X (left..right) : rr[1] =< rr[2]} }
-----------------------------------------------------------------------------
(***************************************************************************)
(* Declare tpMap to be the TPMap and tpLoc the Location that are the       *)
(* inputs to the algorithm.                                                *)
(***************************************************************************)
CONSTANT tpMap, tpRegion
  
(***************************************************************************
                          The Mapping Algorithm

This algorithm sets the variable `result' to the sequence of regions in
the PCal code that, according to the mapping specification tpMap,
should be highlighted when the user selects the region that is the
value of variable tpregion.  (Variable tpregion is initialized to
tpRegion to test a single region, and to SpecToRegions(tpMap) to test
all subregions.) In the initial Java implementation, I expect that
result will be set to a sequence containing only a single region.
                          
--fair algorithm Map {
    variables  
        tpregion \* = tpRegion ,             
                 \in SpecToRegions(tpMap),  
        ltok,      \* <<ltok, rtok>> is set to 
        rtok,      \*   RegionToTokPair(tpMap, tpregion)
        rtokDepth, \* The paren depth of rtok relative to ltok
        minDepth,  \* The depth of the minimum paren depth TLAToken 
        allExpr,   \* Set to true iff all tokens from ltok to rtok are
                   \*   expression tokens.             
        bParen,    \* <<bParen, eParen>> is set to 
        eParen,    \*   TokPairToParens(tpMap, ltok, rtok)
        result,    \* Set to the sequence of Regions that is the translation.
        curBegin,  \* Used to construct the result
        lastRparen,\*  "    
        i,         \* For loop variable
        curDepth ; \* Temporary variable for holding the paren depth

    (***********************************************************************)
    (* If var is the parenthesis depth of the token at position pos, then  *)
    (* the following macro sets var to the parenthesis depth of the token  *)
    (* at position pos + 1 if movingForward = TRUE, else the depth at pos  *)
    (* - 1 if movingForward = FALSE.                                       *)
    (***********************************************************************)
    macro ModifyDepth(var, pos, movingForward) {
      with (amt = CASE tpMap[pos].type = "begin" ->  1  []
                        tpMap[pos].type = "end"   -> -1 []
                        OTHER                    -> 0     ) {
           var := var + IF movingForward THEN amt ELSE -amt
        }
      }
      
    { with (tp = RegionToTokPair(tpMap, tpregion)) {
         ltok := tp[1];
         rtok := tp[2]
       } ;

      (*********************************************************************)
      (* If d is the depth of ltok, then set rtokDepth and minDepth such   *)
      (* that d + rtokDepth is the depth of rtok, d + minDepth is the      *)
      (* minimum depth of tokens, and allExpr is true iff all tokens in    *)
      (* positions ltok to rtok are expression tokens.                     *)
      (*********************************************************************)
      rtokDepth := 0;
      minDepth := 0 ;
      allExpr := tpMap[ltok].inExpr ;
      i := ltok+1;
      while (i =< rtok) {
         ModifyDepth(rtokDepth, i, TRUE);
         if (rtokDepth < minDepth) {minDepth := rtokDepth} ;
         if (tpMap[i].type = "token") {
           allExpr := allExpr /\ tpMap[i].inExpr
          } ;
         i := i+1
       };
       
      assert /\ ParenDepth(tpMap, rtok) = ParenDepth(tpMap, ltok) + rtokDepth
             /\ minDepth + ParenDepth(tpMap, ltok) =
                  Min({ParenDepth(tpMap, k) : k \in ltok..rtok}) 
             /\ allExpr = \A k \in ltok..rtok : 
                             (tpMap[k].type = "token") => tpMap[k].inExpr ;
                             
      (*********************************************************************)
      (* Increment minDepth if ltok # rtok and allExpr is true.            *)
      (*                                                                   *)
      (* This appears to be an error, because the implementation works     *)
      (* properly without the ltok # rtok conjunct in the `if' test.  I    *)
      (* probably didn't test the spec adequately.  However, it's also     *)
      (* possible that the spec is correct and for some subtle reason, the *)
      (* obvious implementation of the `if' test doesn't actually          *)
      (* implement the spec.  As long as the implementation seems to be    *)
      (* working, I don't want to spend the time figuring out what's going *)
      (* on.                                                               *)
      (*********************************************************************)
      if (ltok # rtok /\ allExpr) {minDepth := minDepth + 1} ;
      
      (*********************************************************************)
      (* Set bParen to first left paren to left of ltok that descends to   *)
      (* relative paren depth minDepth.                                    *)
      (*********************************************************************)
      curDepth := 0;
      i := ltok - 1;
      while (~ /\ tpMap[i].type = "begin"
               /\ curDepth = minDepth ) {
        ModifyDepth(curDepth, i, FALSE) ;
        i := i-1
       } ;
      bParen := i ;
      
      (*********************************************************************)
      (* Set eParen to first right paren to the right of rtok that rises   *)
      (* from relative paren depth minDepth.                               *)
      (*********************************************************************)
      curDepth := rtokDepth;
      i := rtok + 1;
      while (~ /\ tpMap[i].type = "end"
               /\ curDepth = minDepth ) {
        ModifyDepth(curDepth, i, TRUE) ;
        i := i+1
       } ;
      eParen := i ;
      
      assert <<bParen, eParen>> = TokPairToParens(tpMap, ltok, rtok);
      
      (*********************************************************************)
      (* Construct the final result.                                       *)
      (*********************************************************************)
      result := << >> ; 
      curBegin := tpMap[bParen].loc ;
      curDepth := 0 ;
      lastRparen := -1 ;
      i := bParen + 1 ;
      while (i < eParen) {
        if (tpMap[i].type = "end") {
          lastRparen := i
          } ;
        if ( /\ tpMap[i].type = "break"
             /\ tpMap[i].depth - curDepth >= 0 ) {
             assert lastRparen # -1 ;
      
             (**************************************************************)
             (* The following statement will be eliminated in the initial  *)
             (* implementation.                                            *)
             (**************************************************************)
             result := Append(result, 
                              [begin |-> curBegin, end |-> tpMap[lastRparen].loc]);

             lastRparen := -1 ;
             while (tpMap[i].type # "begin") {
               ModifyDepth(curDepth, i, TRUE) ;
               i := i+1;
              } ;
             curBegin := tpMap[i].loc ;         
           } ;
        ModifyDepth(curDepth, i, TRUE) ;
        i := i+1;
       } ;
      result := Append(result, 
                       [begin |-> curBegin, end |-> tpMap[eParen].loc]);
      
      \* debugging output
      print <<tpregion.begin.column, tpregion.end.column>> ;
      print [j \in 1..Len(result) |-> <<result[j].begin.column,
                                        result[j].end.column>>];
      print << "lrtok", ltok, rtok>>
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES tpregion, ltok, rtok, rtokDepth, minDepth, allExpr, bParen, eParen, 
          result, curBegin, lastRparen, i, curDepth, pc

vars == << tpregion, ltok, rtok, rtokDepth, minDepth, allExpr, bParen, eParen, 
           result, curBegin, lastRparen, i, curDepth, pc >>

Init == (* Global variables *)
        /\ tpregion \in SpecToRegions(tpMap)
        /\ ltok = defaultInitValue
        /\ rtok = defaultInitValue
        /\ rtokDepth = defaultInitValue
        /\ minDepth = defaultInitValue
        /\ allExpr = defaultInitValue
        /\ bParen = defaultInitValue
        /\ eParen = defaultInitValue
        /\ result = defaultInitValue
        /\ curBegin = defaultInitValue
        /\ lastRparen = defaultInitValue
        /\ i = defaultInitValue
        /\ curDepth = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ LET tp == RegionToTokPair(tpMap, tpregion) IN
              /\ ltok' = tp[1]
              /\ rtok' = tp[2]
         /\ rtokDepth' = 0
         /\ minDepth' = 0
         /\ allExpr' = tpMap[ltok'].inExpr
         /\ i' = ltok'+1
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << tpregion, bParen, eParen, result, curBegin, 
                         lastRparen, curDepth >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i =< rtok
               THEN /\ LET amt == CASE tpMap[i].type = "begin" ->  1  []
                                        tpMap[i].type = "end"   -> -1 []
                                        OTHER                    -> 0 IN
                         rtokDepth' = rtokDepth + IF TRUE THEN amt ELSE -amt
                    /\ IF rtokDepth' < minDepth
                          THEN /\ minDepth' = rtokDepth'
                          ELSE /\ TRUE
                               /\ UNCHANGED minDepth
                    /\ IF tpMap[i].type = "token"
                          THEN /\ allExpr' = (allExpr /\ tpMap[i].inExpr)
                          ELSE /\ TRUE
                               /\ UNCHANGED allExpr
                    /\ i' = i+1
                    /\ pc' = "Lbl_2"
                    /\ UNCHANGED curDepth
               ELSE /\ Assert(/\ ParenDepth(tpMap, rtok) = ParenDepth(tpMap, ltok) + rtokDepth
                              /\ minDepth + ParenDepth(tpMap, ltok) =
                                   Min({ParenDepth(tpMap, k) : k \in ltok..rtok})
                              /\ allExpr = \A k \in ltok..rtok :
                                              (tpMap[k].type = "token") => tpMap[k].inExpr, 
                              "Failure of assertion at line 397, column 7.")
                    /\ IF ltok # rtok /\ allExpr
                          THEN /\ minDepth' = minDepth + 1
                          ELSE /\ TRUE
                               /\ UNCHANGED minDepth
                    /\ curDepth' = 0
                    /\ i' = ltok - 1
                    /\ pc' = "Lbl_3"
                    /\ UNCHANGED << rtokDepth, allExpr >>
         /\ UNCHANGED << tpregion, ltok, rtok, bParen, eParen, result, 
                         curBegin, lastRparen >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ IF ~ /\ tpMap[i].type = "begin"
                 /\ curDepth = minDepth
               THEN /\ LET amt == CASE tpMap[i].type = "begin" ->  1  []
                                        tpMap[i].type = "end"   -> -1 []
                                        OTHER                    -> 0 IN
                         curDepth' = curDepth + IF FALSE THEN amt ELSE -amt
                    /\ i' = i-1
                    /\ pc' = "Lbl_3"
                    /\ UNCHANGED bParen
               ELSE /\ bParen' = i
                    /\ curDepth' = rtokDepth
                    /\ i' = rtok + 1
                    /\ pc' = "Lbl_4"
         /\ UNCHANGED << tpregion, ltok, rtok, rtokDepth, minDepth, allExpr, 
                         eParen, result, curBegin, lastRparen >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ IF ~ /\ tpMap[i].type = "end"
                 /\ curDepth = minDepth
               THEN /\ LET amt == CASE tpMap[i].type = "begin" ->  1  []
                                        tpMap[i].type = "end"   -> -1 []
                                        OTHER                    -> 0 IN
                         curDepth' = curDepth + IF TRUE THEN amt ELSE -amt
                    /\ i' = i+1
                    /\ pc' = "Lbl_4"
                    /\ UNCHANGED << eParen, result, curBegin, lastRparen >>
               ELSE /\ eParen' = i
                    /\ Assert(<<bParen, eParen'>> = TokPairToParens(tpMap, ltok, rtok), 
                              "Failure of assertion at line 434, column 7.")
                    /\ result' = << >>
                    /\ curBegin' = tpMap[bParen].loc
                    /\ curDepth' = 0
                    /\ lastRparen' = -1
                    /\ i' = bParen + 1
                    /\ pc' = "Lbl_5"
         /\ UNCHANGED << tpregion, ltok, rtok, rtokDepth, minDepth, allExpr, 
                         bParen >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ IF i < eParen
               THEN /\ IF tpMap[i].type = "end"
                          THEN /\ lastRparen' = i
                          ELSE /\ TRUE
                               /\ UNCHANGED lastRparen
                    /\ IF /\ tpMap[i].type = "break"
                          /\ tpMap[i].depth - curDepth >= 0
                          THEN /\ Assert(lastRparen' # -1, 
                                         "Failure of assertion at line 450, column 14.")
                               /\ result' = Append(result,
                                                   [begin |-> curBegin, end |-> tpMap[lastRparen'].loc])
                               /\ pc' = "Lbl_6"
                          ELSE /\ pc' = "Lbl_8"
                               /\ UNCHANGED result
               ELSE /\ result' = Append(result,
                                        [begin |-> curBegin, end |-> tpMap[eParen].loc])
                    /\ PrintT(<<tpregion.begin.column, tpregion.end.column>>)
                    /\ PrintT([j \in 1..Len(result') |-> <<result'[j].begin.column,
                                                           result'[j].end.column>>])
                    /\ PrintT(<< "lrtok", ltok, rtok>>)
                    /\ pc' = "Done"
                    /\ UNCHANGED lastRparen
         /\ UNCHANGED << tpregion, ltok, rtok, rtokDepth, minDepth, allExpr, 
                         bParen, eParen, curBegin, i, curDepth >>

Lbl_8 == /\ pc = "Lbl_8"
         /\ LET amt == CASE tpMap[i].type = "begin" ->  1  []
                             tpMap[i].type = "end"   -> -1 []
                             OTHER                    -> 0 IN
              curDepth' = curDepth + IF TRUE THEN amt ELSE -amt
         /\ i' = i+1
         /\ pc' = "Lbl_5"
         /\ UNCHANGED << tpregion, ltok, rtok, rtokDepth, minDepth, allExpr, 
                         bParen, eParen, result, curBegin, lastRparen >>

Lbl_6 == /\ pc = "Lbl_6"
         /\ lastRparen' = -1
         /\ pc' = "Lbl_7"
         /\ UNCHANGED << tpregion, ltok, rtok, rtokDepth, minDepth, allExpr, 
                         bParen, eParen, result, curBegin, i, curDepth >>

Lbl_7 == /\ pc = "Lbl_7"
         /\ IF tpMap[i].type # "begin"
               THEN /\ LET amt == CASE tpMap[i].type = "begin" ->  1  []
                                        tpMap[i].type = "end"   -> -1 []
                                        OTHER                    -> 0 IN
                         curDepth' = curDepth + IF TRUE THEN amt ELSE -amt
                    /\ i' = i+1
                    /\ pc' = "Lbl_7"
                    /\ UNCHANGED curBegin
               ELSE /\ curBegin' = tpMap[i].loc
                    /\ pc' = "Lbl_8"
                    /\ UNCHANGED << i, curDepth >>
         /\ UNCHANGED << tpregion, ltok, rtok, rtokDepth, minDepth, allExpr, 
                         bParen, eParen, result, lastRparen >>

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ Lbl_5 \/ Lbl_8 \/ Lbl_6
           \/ Lbl_7
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Mon Jan 09 15:51:06 PST 2012 by lamport
\* Created Thu Dec 01 16:51:23 PST 2011 by lamport
