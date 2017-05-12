\begin{tla}
-------------------------- MODULE OpenAddressing --------------------------
EXTENDS Sequences, FiniteSets, Integers, TLC

(***************************************************************************)
(* K: The overall number of fingerprints that fit into the table.          *)
(* fps: The set of fingerprints to be inserted into the hash table.        *)
(* empty: An empty (model) value. Used to mark an unoccupied table element.*)
(* N: The number of processes/threads which insert fingerprints. L: The    *)
(* probing limit.                                                          *) 
(***************************************************************************)
CONSTANT K, fps, empty, Procs, L

(***************************************************************************)
(* K is a positive natural.  emtpy is disjunct to all elements in fps.     *)
(* fingerprints are natural numbers and can be well-ordered.               *)
(***************************************************************************)
ASSUME /\ K \in (Nat \ {0})
       /\ \A fp \in fps: fp \in (Nat \ {0})
       /\ empty \notin fps
       /\ (2*L) <= K 
\*       /\ N \in (Nat \ {0})
          
(***************************************************************************)
(* We define Procs to be the set {1, 2, ...  , N} of processes.            *)
(***************************************************************************)
\*Procs == 1..N

----------------------------------------------------------------------------

(***************************************************************************)
(* The element of position Len(seq) of a sequence seq.                     *)
(***************************************************************************)
last(seq) == seq[Len(seq)]                     

(***************************************************************************)
(* The largest element in the sequence, assuming sequence to be sorted in  *) 
(* ascending order.                                                        *)
(***************************************************************************)
largestElem(sortedSeq) == IF sortedSeq = <<>> THEN 0 ELSE last(sortedSeq)
 
(***************************************************************************)
(* All elements of seq1 smaller than elem and the largest element in seq2. *)
(***************************************************************************)
subSetSmaller(seq1, seq2, elem) == SelectSeq(seq1, LAMBDA p:
                                     p < elem /\ p > largestElem(seq2))               

(***************************************************************************)
(* All elements of seq1 larger than the largest element in seq2.           *)
(***************************************************************************)
subSetLarger(seq1, seq2) == IF seq2 = <<>> 
                            THEN seq1 
                            ELSE SelectSeq(seq1, LAMBDA p:
                                                    p > largestElem(seq2))               

(***************************************************************************)
(* TRUE iff the sequence seq contains the element elem.                    *)
(***************************************************************************)
containsElem(seq, elem) == \E i \in 1..Len(seq): seq[i] = elem
                    
(***************************************************************************)
(* The minimum and maximum element in set s.                               *)
(***************************************************************************)
min(S) == CHOOSE s \in S: \A a \in S: s <= a 
max(S) == CHOOSE s \in S: \A a \in S: s >= a 
                     
(***************************************************************************)
(* The given index i modulo the sequences' length.                         *)
(***************************************************************************)
mod(i,len) == IF i % len = 0 THEN len ELSE (i % len)
 
(***************************************************************************)
(* Logical bit-shifting to the right (shifts in zeros from the left/MSB).  *)
(* TLC's standard division does not round towards zero, thus this is       *)
(* specified recursively, manually taking care of rounding.                *)
(***************************************************************************)
RECURSIVE shiftR(_,_)
shiftR(n,pos) == IF pos = 0 THEN n
                 ELSE LET odd(z) == z % 2 = 1
                          m == IF odd(n) THEN (n-1) \div 2 ELSE n \div 2
                      IN shiftR(m, pos - 1)

(***************************************************************************)
(* Bitshifting (faster for any real implementation).                       *)
(***************************************************************************)
bitshift(fp, p) == LET k == CHOOSE k \in 1..K: 2^k = K
                   IN mod(shiftR(fp, k - 1) + 1 + p, K)

(***************************************************************************)
(* Re-scale.                                                               *)
(***************************************************************************) 
rescale(k,maxF,minF,fp,p) == LET f == (k - 1) \div (maxF - minF)
                             IN mod((f * (fp - minF + 1)) + p, k)

(***************************************************************************)
(* Calculates an fp's index where fp \in fps. p is an alternative address, *)
(* such that: p \in 0..P. Uses bitshifting iff K is power of two.          *)
(***************************************************************************)
idx(fp, p) == rescale(K, max(fps), min(fps), fp, p)

(***************************************************************************)
(* TRUE iff the fingerprint at table position index is equal to fp or its  *)
(* corresponding negative fp value (marked as to be copied to secondary).  *)
(***************************************************************************)
isMatch(fp, index, table) == \/ table[index] = fp
                             \/ table[index] = (-1*fp)
                         
----------------------------------------------------------------------------

(***************************************************************************)
(* A fp wrapped around if its alternate indices are beyond K and its       *)
(* actual index is lower than its primary idx.                             *)
(***************************************************************************)
\* wraps might be better called circular because we essentially treat the 
\* array as a circular list.
wrapped(fp, pos, P) == /\ idx(fp,0) + P > K
                       /\ idx(fp,0) > mod(pos, K)

(***************************************************************************)
(* TRUE iff the given two fingerprints have to be swapped to satisfy the   *)
(* expected order.                                                         *)
(***************************************************************************)
compare(fp1,i1,fp2,i2, P) == \/ /\ fp1 < fp2
                                /\ mod(i1, K) > mod(i1+i2, K) 
                                /\ wrapped(fp1,i1, P) <=> wrapped(fp2,i1+i2, P)
                             \/ /\ fp1 > fp2
                                /\ mod(i1, K) > mod(i1+i2, K)
                                /\ idx(fp1,0) = idx(fp2, 0)
                             \/ /\ fp1 > fp2
                                /\ mod(i1, K) < mod(i1+i2, K)
                                /\ idx(fp1,0) >= idx(fp2, 0)
                                /\ wrapped(fp1,i1, P) <=> wrapped(fp2,i1+i2, P)
                             \/ /\ fp1 > fp2
                                /\ mod(i1, K) > mod(i1+i2, K)
                                /\ idx(fp1,0) > idx(fp2, 0)
                                /\ ~(wrapped(fp1,i1, P) <=> wrapped(fp2,i1+i2, P))

----------------------------------------------------------------------------

(***       this is a comment containing the PlusCal code *
--fair algorithm OpenAddressing 
(***************************************************************************)
(* table: The actual hash table specified as a TLA+ sequence. history: An  *)
(* auxiliary (history) variable unrelated to the actual hash table         *)
(* specification. It just records the inserted fingerprints to be verified *)
(* by Inv. An implementation won't need history. secondary: The secondary  *)
(* storage where fingerprints are eventually evicted to. outer/inner:      *)
(* Index variables local to the sort action. P: The number of times an     *) 
(* alterante index is to be tried.                                         *)          
(***************************************************************************)
{ variable table = [i \in 1..K |-> empty], 
           secondary = <<>>, newsecondary = <<>>,
           outer = 1, inner = 1,
           P = 0,
           evict = FALSE,
           history = {};
           
  (* Atomically compare and swap. *)      
   macro CAS(result, pos, expected, new) {
     if (table[pos] = expected) {
         table[pos] := new;
         result := TRUE
    } else { 
         result := FALSE
    }
  }         
     
  (* Compare and swap of two positionss. Positions need not be adjacent to each other. *)      
  macro CASN(result, pos1, pos2, expected1, expected2, new1, new2) {
     if (table[pos1] = expected1 /\ table[pos2] = expected2) {
         table[pos1] := new1 || table[pos2] := new2;
         result := TRUE
    } else { 
         result := FALSE
    }
  }         
           
  fair process (p \in Procs)
    variables fp = 0,
              index = 0, 
              freePos = -1,
              result = FALSE,
              expected1 = -1;
              expected2 = -1;
    {
     lbl00:  while (TRUE) {
              \* No deadlock when all fingerprints have been inserted.
              if ((fps \ history) = {}) {
                goto Done;
              };
              \* Select a fp to be inserted
     lbl01:   with (f \in (fps \ history)) { fp := f; };
     
              \* contains(fp)
     cntns:   index := 0;
              freePos := -1;
              result := FALSE;
              expected1 := -1;
              expected2 := -1;
     loop1:   while (index < P) {
               if (isMatch(fp, idx(fp, index), table)) {
                goto lbl00
               } else {
                index:=index+1
               }
              };
              \* Reset index to 0 after cntns for insrt to start trying from position 0.
              index := 0;
              
              \* secondary lookup
     onSnc:   if (containsElem(secondary,fp)) {
                goto lbl00
              };
              
              
              (* Put inserts the given fp into the hash table by sequentially trying *)
              (* the primary to the P's alternate position.                          *)
     insrt:   while (index < L) {
               \* Empty position, insert right away
     iempt:    if (table[idx(fp,index)] = empty) {
                 \* Increment P before setting fp. Otherwise, there is a small window during which the fp cannot be found.
     incP1:      if (index > P) {P := index};
     set01:      CAS(result, idx(fp,index), empty, fp);
                 if (result) {
                   history := history \cup {fp};
                   goto lbl00
                 } else {
                   \* Check if CAS failed because another thread inserted the same fp
                   if (index > 0) {
                     index := index - 1;
                   };
                   goto insrt
                 }
               };
               
               \* Has fp been inserted by another process? Check isMatch AFTER
               \* empty because of two reasons:
               \* a) Thread A finds table[pos] to be empty but fails to CAS fp_x. 
               \*    Thread B concurrently also finds table[pos] to be empty and
               \*    succeeds to CAS fp_x.
               \* b) Iff table[pos] is empty, higher positions cannot be a match.
     isMth1:   if (isMatch(fp,idx(fp,index),table)) {
                 goto lbl00
               };
               
               \* A secondary copied position, remember it as candidate.
     mSncd:    if (table[idx(fp,index)] < 0)  {
                 freePos := idx(fp,index);
                 expected1 := table[idx(fp,index)];
                 index := index+1
               } else {
                 index := index+1
               };
               
               \* CAS at freePos
     freePo:   if (freePos > -1) {
                 \* Increment P before setting fp. Otherwise, there is a small window during which the fp cannot be found.
     incP2:      if (index > P) {P := index};
     set02:      CAS(result, freePos, expected1, fp);
                 if (result) {
                   history := history \cup {fp};
                   goto lbl00
                 } else {
                  \* Has been occupied in the meantime, try to find another position
                  goto cntns
                 }
                } 
               };
               
               \* Checking and flipping evict is essentially CAS too
     canEv:    if (evict = FALSE) {
                \* Become the thread that evicts to secondary
                 evict := ~evict;
                 (* For every element with index i in ascending order of table, sort the *)
                 (* elements in the range i..i+P. The range can be seen as a lookahead. *)
     strEv:      while (outer+inner <= K+(2*(P+1))) {
     read1:       expected1 := table[mod(outer, K)];
     read2:       expected2 := table[mod(outer+inner, K)];
     cmpEv:       if (expected1 # empty /\ expected2 # empty /\
                      expected1 > 0 /\ expected2 > 0 /\
                      compare(expected1,outer,expected2,inner, P)) {
                      \* We don't swap fingerprints that can be changed by other threads. Evict swaps fingerprints
                      \* which are in primary storage. Other threads write to empty positions or fingerprints marked
                      \* as being on secondary storage. Still, swap has to be atomically to not violate Inv. 
     dcas1:           CASN(result, mod(outer, K), mod(outer+inner, K), expected1, expected2, expected2, expected1);
                      assert result;
                  };
     incVr:       if (inner + 1 > P) {
                   (* Write table[mod(cpy,table)] to secondary. *)
     swpEv:        expected1 := table[mod(outer, K)];
                   if (expected1 # empty /\
                       expected1 > largestElem(newsecondary) /\
                      ((outer <= K /\ ~wrapped(expected1,outer,P)) \/ 
                       (outer > K /\ wrapped(expected1,outer,P)))) {
                     (* Copy all smaller fps than expected1 from secondary to newsecondary. *)
                     newsecondary := Append(newsecondary \o subSetSmaller(secondary, newsecondary, expected1), expected1);
                     (* Mark table[mod(cpy,table)] as being written to secondary. *)
                     table[mod(outer, K)] := expected1 * (-1);
                   };
                   (* Update outer and inner. *)
                   inner := 1;
                   outer := outer + 1;
                  } else {
                    (* Update inner. *)
                    inner := inner + 1
                  }
                 };
                 (* Append remainder of secondary to newsecondary and assign newsecondary to secondary. *)
                 secondary := newsecondary \o subSetLarger(secondary, newsecondary);
                 newsecondary := <<>>;
                 outer := 1;
                 inner := 1;
     endEv:     evict := ~evict;
                 goto cntns;                   
                } else {
                 goto cntns
                }
              }
             }
    }
}
***     this ends the comment containg the pluscal code      **********)
\* BEGIN TRANSLATION
VARIABLES table, secondary, newsecondary, outer, inner, P, evict, history, pc, 
          fp, index, freePos, result, expected1, expected2

vars == << table, secondary, newsecondary, outer, inner, P, evict, history, 
           pc, fp, index, freePos, result, expected1, expected2 >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ table = [i \in 1..K |-> empty]
        /\ secondary = <<>>
        /\ newsecondary = <<>>
        /\ outer = 1
        /\ inner = 1
        /\ P = 0
        /\ evict = FALSE
        /\ history = {}
        (* Process p *)
        /\ fp = [self \in Procs |-> 0]
        /\ index = [self \in Procs |-> 0]
        /\ freePos = [self \in Procs |-> -1]
        /\ result = [self \in Procs |-> FALSE]
        /\ expected1 = [self \in Procs |-> -1]
        /\ expected2 = [self \in Procs |-> -1]
        /\ pc = [self \in ProcSet |-> "lbl00"]

lbl00(self) == /\ pc[self] = "lbl00"
               /\ IF (fps \ history) = {}
                     THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "lbl01"]
               /\ UNCHANGED << table, secondary, newsecondary, outer, inner, P, 
                               evict, history, fp, index, freePos, result, 
                               expected1, expected2 >>

lbl01(self) == /\ pc[self] = "lbl01"
               /\ \E f \in (fps \ history):
                    fp' = [fp EXCEPT ![self] = f]
               /\ pc' = [pc EXCEPT ![self] = "cntns"]
               /\ UNCHANGED << table, secondary, newsecondary, outer, inner, P, 
                               evict, history, index, freePos, result, 
                               expected1, expected2 >>

cntns(self) == /\ pc[self] = "cntns"
               /\ index' = [index EXCEPT ![self] = 0]
               /\ freePos' = [freePos EXCEPT ![self] = -1]
               /\ result' = [result EXCEPT ![self] = FALSE]
               /\ expected1' = [expected1 EXCEPT ![self] = -1]
               /\ expected2' = [expected2 EXCEPT ![self] = -1]
               /\ pc' = [pc EXCEPT ![self] = "loop1"]
               /\ UNCHANGED << table, secondary, newsecondary, outer, inner, P, 
                               evict, history, fp >>

loop1(self) == /\ pc[self] = "loop1"
               /\ IF index[self] < P
                     THEN /\ IF isMatch(fp[self], idx(fp[self], index[self]), table)
                                THEN /\ pc' = [pc EXCEPT ![self] = "lbl00"]
                                     /\ index' = index
                                ELSE /\ index' = [index EXCEPT ![self] = index[self]+1]
                                     /\ pc' = [pc EXCEPT ![self] = "loop1"]
                     ELSE /\ index' = [index EXCEPT ![self] = 0]
                          /\ pc' = [pc EXCEPT ![self] = "onSnc"]
               /\ UNCHANGED << table, secondary, newsecondary, outer, inner, P, 
                               evict, history, fp, freePos, result, expected1, 
                               expected2 >>

onSnc(self) == /\ pc[self] = "onSnc"
               /\ IF containsElem(secondary,fp[self])
                     THEN /\ pc' = [pc EXCEPT ![self] = "lbl00"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "insrt"]
               /\ UNCHANGED << table, secondary, newsecondary, outer, inner, P, 
                               evict, history, fp, index, freePos, result, 
                               expected1, expected2 >>

insrt(self) == /\ pc[self] = "insrt"
               /\ IF index[self] < L
                     THEN /\ pc' = [pc EXCEPT ![self] = "iempt"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "canEv"]
               /\ UNCHANGED << table, secondary, newsecondary, outer, inner, P, 
                               evict, history, fp, index, freePos, result, 
                               expected1, expected2 >>

iempt(self) == /\ pc[self] = "iempt"
               /\ IF table[idx(fp[self],index[self])] = empty
                     THEN /\ pc' = [pc EXCEPT ![self] = "incP1"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "isMth1"]
               /\ UNCHANGED << table, secondary, newsecondary, outer, inner, P, 
                               evict, history, fp, index, freePos, result, 
                               expected1, expected2 >>

incP1(self) == /\ pc[self] = "incP1"
               /\ IF index[self] > P
                     THEN /\ P' = index[self]
                     ELSE /\ TRUE
                          /\ P' = P
               /\ pc' = [pc EXCEPT ![self] = "set01"]
               /\ UNCHANGED << table, secondary, newsecondary, outer, inner, 
                               evict, history, fp, index, freePos, result, 
                               expected1, expected2 >>

set01(self) == /\ pc[self] = "set01"
               /\ IF table[(idx(fp[self],index[self]))] = empty
                     THEN /\ table' = [table EXCEPT ![(idx(fp[self],index[self]))] = fp[self]]
                          /\ result' = [result EXCEPT ![self] = TRUE]
                     ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                          /\ table' = table
               /\ IF result'[self]
                     THEN /\ history' = (history \cup {fp[self]})
                          /\ pc' = [pc EXCEPT ![self] = "lbl00"]
                          /\ index' = index
                     ELSE /\ IF index[self] > 0
                                THEN /\ index' = [index EXCEPT ![self] = index[self] - 1]
                                ELSE /\ TRUE
                                     /\ index' = index
                          /\ pc' = [pc EXCEPT ![self] = "insrt"]
                          /\ UNCHANGED history
               /\ UNCHANGED << secondary, newsecondary, outer, inner, P, evict, 
                               fp, freePos, expected1, expected2 >>

isMth1(self) == /\ pc[self] = "isMth1"
                /\ IF isMatch(fp[self],idx(fp[self],index[self]),table)
                      THEN /\ pc' = [pc EXCEPT ![self] = "lbl00"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "mSncd"]
                /\ UNCHANGED << table, secondary, newsecondary, outer, inner, 
                                P, evict, history, fp, index, freePos, result, 
                                expected1, expected2 >>

mSncd(self) == /\ pc[self] = "mSncd"
               /\ IF table[idx(fp[self],index[self])] < 0
                     THEN /\ freePos' = [freePos EXCEPT ![self] = idx(fp[self],index[self])]
                          /\ expected1' = [expected1 EXCEPT ![self] = table[idx(fp[self],index[self])]]
                          /\ index' = [index EXCEPT ![self] = index[self]+1]
                     ELSE /\ index' = [index EXCEPT ![self] = index[self]+1]
                          /\ UNCHANGED << freePos, expected1 >>
               /\ pc' = [pc EXCEPT ![self] = "freePo"]
               /\ UNCHANGED << table, secondary, newsecondary, outer, inner, P, 
                               evict, history, fp, result, expected2 >>

freePo(self) == /\ pc[self] = "freePo"
                /\ IF freePos[self] > -1
                      THEN /\ pc' = [pc EXCEPT ![self] = "incP2"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "insrt"]
                /\ UNCHANGED << table, secondary, newsecondary, outer, inner, 
                                P, evict, history, fp, index, freePos, result, 
                                expected1, expected2 >>

incP2(self) == /\ pc[self] = "incP2"
               /\ IF index[self] > P
                     THEN /\ P' = index[self]
                     ELSE /\ TRUE
                          /\ P' = P
               /\ pc' = [pc EXCEPT ![self] = "set02"]
               /\ UNCHANGED << table, secondary, newsecondary, outer, inner, 
                               evict, history, fp, index, freePos, result, 
                               expected1, expected2 >>

set02(self) == /\ pc[self] = "set02"
               /\ IF table[freePos[self]] = expected1[self]
                     THEN /\ table' = [table EXCEPT ![freePos[self]] = fp[self]]
                          /\ result' = [result EXCEPT ![self] = TRUE]
                     ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                          /\ table' = table
               /\ IF result'[self]
                     THEN /\ history' = (history \cup {fp[self]})
                          /\ pc' = [pc EXCEPT ![self] = "lbl00"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "cntns"]
                          /\ UNCHANGED history
               /\ UNCHANGED << secondary, newsecondary, outer, inner, P, evict, 
                               fp, index, freePos, expected1, expected2 >>

canEv(self) == /\ pc[self] = "canEv"
               /\ IF evict = FALSE
                     THEN /\ evict' = ~evict
                          /\ pc' = [pc EXCEPT ![self] = "strEv"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "cntns"]
                          /\ evict' = evict
               /\ UNCHANGED << table, secondary, newsecondary, outer, inner, P, 
                               history, fp, index, freePos, result, expected1, 
                               expected2 >>

strEv(self) == /\ pc[self] = "strEv"
               /\ IF outer+inner <= K+(2*(P+1))
                     THEN /\ pc' = [pc EXCEPT ![self] = "read1"]
                          /\ UNCHANGED << secondary, newsecondary, outer, 
                                          inner >>
                     ELSE /\ secondary' = newsecondary \o subSetLarger(secondary, newsecondary)
                          /\ newsecondary' = <<>>
                          /\ outer' = 1
                          /\ inner' = 1
                          /\ pc' = [pc EXCEPT ![self] = "endEv"]
               /\ UNCHANGED << table, P, evict, history, fp, index, freePos, 
                               result, expected1, expected2 >>

read1(self) == /\ pc[self] = "read1"
               /\ expected1' = [expected1 EXCEPT ![self] = table[mod(outer, K)]]
               /\ pc' = [pc EXCEPT ![self] = "read2"]
               /\ UNCHANGED << table, secondary, newsecondary, outer, inner, P, 
                               evict, history, fp, index, freePos, result, 
                               expected2 >>

read2(self) == /\ pc[self] = "read2"
               /\ expected2' = [expected2 EXCEPT ![self] = table[mod(outer+inner, K)]]
               /\ pc' = [pc EXCEPT ![self] = "cmpEv"]
               /\ UNCHANGED << table, secondary, newsecondary, outer, inner, P, 
                               evict, history, fp, index, freePos, result, 
                               expected1 >>

cmpEv(self) == /\ pc[self] = "cmpEv"
               /\ IF expected1[self] # empty /\ expected2[self] # empty /\
                     expected1[self] > 0 /\ expected2[self] > 0 /\
                     compare(expected1[self],outer,expected2[self],inner, P)
                     THEN /\ pc' = [pc EXCEPT ![self] = "dcas1"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "incVr"]
               /\ UNCHANGED << table, secondary, newsecondary, outer, inner, P, 
                               evict, history, fp, index, freePos, result, 
                               expected1, expected2 >>

dcas1(self) == /\ pc[self] = "dcas1"
               /\ IF table[(mod(outer, K))] = expected1[self] /\ table[(mod(outer+inner, K))] = expected2[self]
                     THEN /\ table' = [table EXCEPT ![(mod(outer, K))] = expected2[self],
                                                    ![(mod(outer+inner, K))] = expected1[self]]
                          /\ result' = [result EXCEPT ![self] = TRUE]
                     ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                          /\ table' = table
               /\ Assert(result'[self], 
                         "Failure of assertion at line 286, column 23.")
               /\ pc' = [pc EXCEPT ![self] = "incVr"]
               /\ UNCHANGED << secondary, newsecondary, outer, inner, P, evict, 
                               history, fp, index, freePos, expected1, 
                               expected2 >>

incVr(self) == /\ pc[self] = "incVr"
               /\ IF inner + 1 > P
                     THEN /\ pc' = [pc EXCEPT ![self] = "swpEv"]
                          /\ inner' = inner
                     ELSE /\ inner' = inner + 1
                          /\ pc' = [pc EXCEPT ![self] = "strEv"]
               /\ UNCHANGED << table, secondary, newsecondary, outer, P, evict, 
                               history, fp, index, freePos, result, expected1, 
                               expected2 >>

swpEv(self) == /\ pc[self] = "swpEv"
               /\ expected1' = [expected1 EXCEPT ![self] = table[mod(outer, K)]]
               /\ IF  expected1'[self] # empty /\
                      expected1'[self] > largestElem(newsecondary) /\
                     ((outer <= K /\ ~wrapped(expected1'[self],outer,P)) \/
                      (outer > K /\ wrapped(expected1'[self],outer,P)))
                     THEN /\ newsecondary' = Append(newsecondary \o subSetSmaller(secondary, newsecondary, expected1'[self]), expected1'[self])
                          /\ table' = [table EXCEPT ![mod(outer, K)] = expected1'[self] * (-1)]
                     ELSE /\ TRUE
                          /\ UNCHANGED << table, newsecondary >>
               /\ inner' = 1
               /\ outer' = outer + 1
               /\ pc' = [pc EXCEPT ![self] = "strEv"]
               /\ UNCHANGED << secondary, P, evict, history, fp, index, 
                               freePos, result, expected2 >>

endEv(self) == /\ pc[self] = "endEv"
               /\ evict' = ~evict
               /\ pc' = [pc EXCEPT ![self] = "cntns"]
               /\ UNCHANGED << table, secondary, newsecondary, outer, inner, P, 
                               history, fp, index, freePos, result, expected1, 
                               expected2 >>

p(self) == lbl00(self) \/ lbl01(self) \/ cntns(self) \/ loop1(self)
              \/ onSnc(self) \/ insrt(self) \/ iempt(self) \/ incP1(self)
              \/ set01(self) \/ isMth1(self) \/ mSncd(self) \/ freePo(self)
              \/ incP2(self) \/ set02(self) \/ canEv(self) \/ strEv(self)
              \/ read1(self) \/ read2(self) \/ cmpEv(self) \/ dcas1(self)
              \/ incVr(self) \/ swpEv(self) \/ endEv(self)

Next == (\E self \in Procs: p(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

(***************************************************************************)
(* A type correctness invariant for outer, inner and P.                    *)
(***************************************************************************)
TypeOK == /\ outer \in (Nat \ {0})
          /\ inner \in (Nat \ {0})
          /\ P \in Nat
          /\ P <= L

(***************************************************************************)
(* TRUE iff fingerprint fp is either found within table according to       *)
(* isMatch or in seq.                                                      *)
(***************************************************************************)
contains(f,t,seq,Q) == \/ \E i \in 0..Q: isMatch(f,idx(f,i),t)
                       \/ \E i \in 1..Len(seq): seq[i] = f 
                        
(***************************************************************************)
(* All fingerprint in history are (always) hash table members,             *)
(* all fps \ history never are.                                            *)
(***************************************************************************)
Inv == /\ \A seen \in history: contains(seen,table,secondary,P+1)
       /\ \A unseen \in (fps \ history): ~contains(unseen,table,secondary,P+1)
       
(***************************************************************************)
(* t is sorted iff its empty-filtered sub-sequence is sorted. An empty     *)
(* sequence is defined to be sorted.                                       *)
(***************************************************************************)
isSorted(seq) == LET sub == SelectSeq(secondary, LAMBDA e: e # empty)
                 IN IF sub = <<>> THEN TRUE
                    ELSE \A i \in 1..(Len(sub) - 1):
                         sub[mod(i, Len(sub))] < sub[mod(i+1, Len(sub))]
                        
(***************************************************************************)
(* Secondary storage is always sorted in ascending order.                  *)
(***************************************************************************) 
Sorted == isSorted(secondary) /\ isSorted(newsecondary)

(***************************************************************************)
(* TRUE iff f is found in table within idx(f,0)..id(f,r).                  *)
(***************************************************************************)
containedInTable(f) == \E r \in 0..P+1: IF f < 0
                                        THEN table[idx((-1)*f, r)] = f
                                        ELSE table[idx(f, r)] = f

(***************************************************************************)
(* TRUE iff f is found in secondary.                                       *)
(***************************************************************************)
containedInSecondary(f) == containsElem(secondary,f)

(***************************************************************************)
(* TRUE iff f is found in newsecondary.                                    *)
(***************************************************************************)
containedInNewSecondary(f) == containsElem(newsecondary,f)

(* TRUE iff: A positive fp is exclusively either in table or secondary. *)
Consistent == \A seen \in history:
        /\ (containedInTable(seen) => ~containedInSecondary(seen))
        /\ (containedInTable(seen) => ~containedInNewSecondary(seen))
        /\ (~containedInTable(seen) => (containedInSecondary(seen)) \/ 
                                        containedInNewSecondary(seen))
        /\ (containedInTable(seen * (-1)) => (containedInSecondary(seen)) \/ 
                                              containedInNewSecondary(seen))
\* not supported by TLC
\*      /\ (containedInTable((-1)*seen) ~> containedInSecondary(seen))

(***************************************************************************)
(* TRUE iff the maximum displacement of all elements equals P. In other    *)
(* words, P is minimal.                                                    *)
(***************************************************************************)
Minimal == FALSE

(***************************************************************************)
(* Eventually, an eviction ends.                                           *)
(***************************************************************************)
EvictEnds == evict = TRUE ~> evict = FALSE

(***************************************************************************)
(* Under all behaviors, secondary is the sorted sequence of history.       *)
(***************************************************************************)
Prop == /\ <>[](history = fps)
        /\ <>[](newsecondary = <<>>)
=============================================================================
\end{tla}
