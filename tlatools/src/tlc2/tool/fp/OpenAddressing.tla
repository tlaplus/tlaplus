\begin{tla}
-------------------------- MODULE OpenAddressing --------------------------
EXTENDS Sequences, FiniteSets, Integers, TLC

(***************************************************************************)
(* K: The overall number of fingerprints that fit into the table.          *)
(* fps: The set of fingerprints to be inserted into the hash table.        *)
(* empty: An empty (model) value. Used to mark an unoccupied table element.*)
(* Procs: The set of processes/threads which insert fingerprints. L: The   *)
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
       
(***************************************************************************)
(* t is sorted iff its empty-filtered sub-sequence is sorted. An empty     *)
(* sequence is defined to be sorted.                                       *)
(***************************************************************************)
isSorted(seq) == LET sub == SelectSeq(seq, LAMBDA e: e # empty)
                 IN IF sub = <<>> THEN TRUE
                    ELSE \A i \in 1..(Len(sub) - 1):
                         sub[mod(i, Len(sub))] < sub[mod(i+1, Len(sub))]

(***************************************************************************)
(* TRUE iff fingerprint fp is either found within table according to       *)
(* isMatch or in seq.                                                      *)
(***************************************************************************)
contains(f,t,seq,Q) == \/ \E i \in 0..Q: isMatch(f,idx(f,i),t)
                       \/ \E i \in 1..Len(seq): seq[i] = f 
                       
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
           secondary = <<>>,
           newsecondary = <<>>,
           P = 0,
           evict = FALSE,
           numEv = 0, \* A modification counter of table (modCnt)
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
     
  (* Compare and swap of two positionss. Positions need not be adjacent to each other.
     (On Java, the only possible way to do CASN is to write a tiny bit of JNI.) *)      
  macro CASN(result, pos1, pos2, expected1, expected2, new1, new2) {
     if (table[pos1] = expected1 /\ table[pos2] = expected2) {
         table[pos1] := new1 || table[pos2] := new2;
         result := TRUE
    } else { 
         result := FALSE
    }
  }    
        
  (* Compare and swap element at positions iff current element at
     table[pos] = expected and evict is FALSE. In a Java
     implementation, evict can be an extension (byte) table
     not used for fingerprints. *)
  macro CASNev(result, expectedEv, pos, expected, new) {
     if (numEv = expectedEv /\ evict = FALSE /\ table[pos] = expected) {
         table[pos] := new;
         result := TRUE
    } else { 
         result := FALSE
    }
  }         
  
  (* Eviction procedure. *)
  procedure Evict()
     variables outer = 1, inner = 1; {
                (* For every element with index i in ascending order of table, sort the *)
                (* elements in the range i..i+P. The range can be seen as a lookahead. *)
     strEv:     while (outer+inner <= K+(2*(P+1))) {
                  expected1 := table[mod(outer, K)];
     read:        expected2 := table[mod(outer+inner, K)];
                  if (expected1 # empty /\ expected2 # empty /\
                      expected1 > 0 /\ expected2 > 0 /\
                      compare(expected1,outer,expected2,inner, P)) {
                      \* We don't swap fingerprints that can be changed by other threads. Evict swaps fingerprints
                      \* which are in primary storage. Other threads write to empty positions or fingerprints marked
                      \* as being on secondary storage. Still, swap has to be atomically to not violate Inv. 
     dcas:            CASN(result, mod(outer, K), mod(outer+inner, K), expected1, expected2, expected2, expected1);
                      assert result;
                  };
     incVr:       if (inner + 1 > P) {
                     (* Write table[mod(cpy,table)] to secondary. *)
     swpEv:          expected1 := table[mod(outer, K)];
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
     rtrn:      return;
  }
       
  (* A weak fair process. *)        
  fair process (p \in Procs)
    variables fp = 0,
              index = 0, 
              freePos = -1,
              result = FALSE,
              expectedEv = 0,
              expected1 = -1;
              expected2 = -1;
    {
    pick:  while (TRUE) {
              \* No deadlock once all fingerprints have been inserted.
              if ((fps \ history) = {}) {
                goto Done;
              } else {
                \* Select a fp to be inserted
                with (f \in (fps \ history)) { fp := f; };
              };
     

     put:     index := 0;
              freePos := -1;
              result := FALSE;
              expectedEv := numEv;
              expected1 := -1;
              expected2 := -1;
              
              (* Primary lookup. *)
     cntns:   while (index < P) {
                if (isMatch(fp, idx(fp, index), table)) {
                  goto pick
                } else {
                  index := index + 1
                }
              };
              \* Reset index to 0 after cntns for insrt to start
              \* trying from position 0. Other threads might have
              \* inserted fp in between cntns and insrt.
              index := 0;
              
              
              (* Secondary lookup. *)
     onSnc:   if (containsElem(secondary,fp)) {
                 goto pick
              };
              
              
              (* Put inserts the given fp into the hash table by sequentially trying *)
              (* the primary to the P's alternate position.                          *)
     insrt:   while (index < L) {
                 expected1 := table[idx(fp,index)];
                 if (expected1 = empty \/ (expected1 < 0 /\ expected1 # (-1) * fp))  {
     incP:           if (index > P) {P := index};
     cas:            CASNev(result, expectedEv, idx(fp,index), expected1, fp);
                     if (result) {
                        history := history \cup {fp};
                        goto pick
                     } else {
                        if (numEv > expectedEv \/ evict) {
                           \* Wait for eviction to end or 
                           \* start from scratch because
                           \* an finished eviction invalidated
                           \* our earlier checkes (contains
                           \* and on-secondray).
                           await ~evict;
                           goto put
                        } else {
                           \* Has been occupied in the meantime,
                           \* try to find another position.
                           goto insrt
                        }
                      }
                 };
                
                 \* Has fp been inserted by another process? Check isMatch AFTER
                 \* empty and on-secondary because of two reasons:
                 \* a) Thread A finds table[pos] to be empty but fails to CAS fp_x. 
                 \*    Thread B concurrently also finds table[pos] to be empty and
                 \*    succeeds to CAS fp_x.
                 \* b) Iff table[pos] is empty or -1, higher positions cannot be a
                 \*    match.
     isMth:      if (isMatch(fp,idx(fp,index),table)) {
                    goto pick
                 } else {
                    index := index + 1;
                 };
              }; \* end of while/insrt


              (* Try to become the thread that evicts to secondary. *)
              (* Checking and flipping evict is essentially CAS too.*)
     tryEv:   if (evict = FALSE) {
                 evict := ~evict;
                 call Evict();
     endEv:      evict := ~evict;
                 numEv := numEv + 1;
                 goto put;                   
               } else {
                 await ~evict;
                 goto put
               }
             } 
           }
    }
}
***     this ends the comment containg the pluscal code      **********)
\* BEGIN TRANSLATION
VARIABLES table, secondary, newsecondary, P, evict, numEv, history, pc, stack, 
          outer, inner, fp, index, freePos, result, expectedEv, expected1, 
          expected2

vars == << table, secondary, newsecondary, P, evict, numEv, history, pc, 
           stack, outer, inner, fp, index, freePos, result, expectedEv, 
           expected1, expected2 >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ table = [i \in 1..K |-> empty]
        /\ secondary = <<>>
        /\ newsecondary = <<>>
        /\ P = 0
        /\ evict = FALSE
        /\ numEv = 0
        /\ history = {}
        (* Procedure Evict *)
        /\ outer = [ self \in ProcSet |-> 1]
        /\ inner = [ self \in ProcSet |-> 1]
        (* Process p *)
        /\ fp = [self \in Procs |-> 0]
        /\ index = [self \in Procs |-> 0]
        /\ freePos = [self \in Procs |-> -1]
        /\ result = [self \in Procs |-> FALSE]
        /\ expectedEv = [self \in Procs |-> 0]
        /\ expected1 = [self \in Procs |-> -1]
        /\ expected2 = [self \in Procs |-> -1]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "pick"]

strEv(self) == /\ pc[self] = "strEv"
               /\ IF outer[self]+inner[self] <= K+(2*(P+1))
                     THEN /\ expected1' = [expected1 EXCEPT ![self] = table[mod(outer[self], K)]]
                          /\ pc' = [pc EXCEPT ![self] = "read"]
                          /\ UNCHANGED << secondary, newsecondary >>
                     ELSE /\ secondary' = newsecondary \o subSetLarger(secondary, newsecondary)
                          /\ newsecondary' = <<>>
                          /\ pc' = [pc EXCEPT ![self] = "rtrn"]
                          /\ UNCHANGED expected1
               /\ UNCHANGED << table, P, evict, numEv, history, stack, outer, 
                               inner, fp, index, freePos, result, expectedEv, 
                               expected2 >>

read(self) == /\ pc[self] = "read"
              /\ expected2' = [expected2 EXCEPT ![self] = table[mod(outer[self]+inner[self], K)]]
              /\ IF expected1[self] # empty /\ expected2'[self] # empty /\
                    expected1[self] > 0 /\ expected2'[self] > 0 /\
                    compare(expected1[self],outer[self],expected2'[self],inner[self], P)
                    THEN /\ pc' = [pc EXCEPT ![self] = "dcas"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "incVr"]
              /\ UNCHANGED << table, secondary, newsecondary, P, evict, numEv, 
                              history, stack, outer, inner, fp, index, freePos, 
                              result, expectedEv, expected1 >>

dcas(self) == /\ pc[self] = "dcas"
              /\ IF table[(mod(outer[self], K))] = expected1[self] /\ table[(mod(outer[self]+inner[self], K))] = expected2[self]
                    THEN /\ table' = [table EXCEPT ![(mod(outer[self], K))] = expected2[self],
                                                   ![(mod(outer[self]+inner[self], K))] = expected1[self]]
                         /\ result' = [result EXCEPT ![self] = TRUE]
                    ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                         /\ table' = table
              /\ Assert(result'[self], 
                        "Failure of assertion at line 218, column 23.")
              /\ pc' = [pc EXCEPT ![self] = "incVr"]
              /\ UNCHANGED << secondary, newsecondary, P, evict, numEv, 
                              history, stack, outer, inner, fp, index, freePos, 
                              expectedEv, expected1, expected2 >>

incVr(self) == /\ pc[self] = "incVr"
               /\ IF inner[self] + 1 > P
                     THEN /\ pc' = [pc EXCEPT ![self] = "swpEv"]
                          /\ inner' = inner
                     ELSE /\ inner' = [inner EXCEPT ![self] = inner[self] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "strEv"]
               /\ UNCHANGED << table, secondary, newsecondary, P, evict, numEv, 
                               history, stack, outer, fp, index, freePos, 
                               result, expectedEv, expected1, expected2 >>

swpEv(self) == /\ pc[self] = "swpEv"
               /\ expected1' = [expected1 EXCEPT ![self] = table[mod(outer[self], K)]]
               /\ IF expected1'[self] # empty /\
                     expected1'[self] > largestElem(newsecondary) /\
                     ((outer[self] <= K /\ ~wrapped(expected1'[self],outer[self],P)) \/
                      (outer[self] > K /\ wrapped(expected1'[self],outer[self],P)))
                     THEN /\ newsecondary' = Append(newsecondary \o subSetSmaller(secondary, newsecondary, expected1'[self]), expected1'[self])
                          /\ table' = [table EXCEPT ![mod(outer[self], K)] = expected1'[self] * (-1)]
                     ELSE /\ TRUE
                          /\ UNCHANGED << table, newsecondary >>
               /\ inner' = [inner EXCEPT ![self] = 1]
               /\ outer' = [outer EXCEPT ![self] = outer[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "strEv"]
               /\ UNCHANGED << secondary, P, evict, numEv, history, stack, fp, 
                               index, freePos, result, expectedEv, expected2 >>

rtrn(self) == /\ pc[self] = "rtrn"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ outer' = [outer EXCEPT ![self] = Head(stack[self]).outer]
              /\ inner' = [inner EXCEPT ![self] = Head(stack[self]).inner]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << table, secondary, newsecondary, P, evict, numEv, 
                              history, fp, index, freePos, result, expectedEv, 
                              expected1, expected2 >>

Evict(self) == strEv(self) \/ read(self) \/ dcas(self) \/ incVr(self)
                  \/ swpEv(self) \/ rtrn(self)

pick(self) == /\ pc[self] = "pick"
              /\ IF (fps \ history) = {}
                    THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ fp' = fp
                    ELSE /\ \E f \in (fps \ history):
                              fp' = [fp EXCEPT ![self] = f]
                         /\ pc' = [pc EXCEPT ![self] = "put"]
              /\ UNCHANGED << table, secondary, newsecondary, P, evict, numEv, 
                              history, stack, outer, inner, index, freePos, 
                              result, expectedEv, expected1, expected2 >>

put(self) == /\ pc[self] = "put"
             /\ index' = [index EXCEPT ![self] = 0]
             /\ freePos' = [freePos EXCEPT ![self] = -1]
             /\ result' = [result EXCEPT ![self] = FALSE]
             /\ expectedEv' = [expectedEv EXCEPT ![self] = numEv]
             /\ expected1' = [expected1 EXCEPT ![self] = -1]
             /\ expected2' = [expected2 EXCEPT ![self] = -1]
             /\ pc' = [pc EXCEPT ![self] = "cntns"]
             /\ UNCHANGED << table, secondary, newsecondary, P, evict, numEv, 
                             history, stack, outer, inner, fp >>

cntns(self) == /\ pc[self] = "cntns"
               /\ IF index[self] < P
                     THEN /\ IF isMatch(fp[self], idx(fp[self], index[self]), table)
                                THEN /\ pc' = [pc EXCEPT ![self] = "pick"]
                                     /\ index' = index
                                ELSE /\ index' = [index EXCEPT ![self] = index[self] + 1]
                                     /\ pc' = [pc EXCEPT ![self] = "cntns"]
                     ELSE /\ index' = [index EXCEPT ![self] = 0]
                          /\ pc' = [pc EXCEPT ![self] = "onSnc"]
               /\ UNCHANGED << table, secondary, newsecondary, P, evict, numEv, 
                               history, stack, outer, inner, fp, freePos, 
                               result, expectedEv, expected1, expected2 >>

onSnc(self) == /\ pc[self] = "onSnc"
               /\ IF containsElem(secondary,fp[self])
                     THEN /\ pc' = [pc EXCEPT ![self] = "pick"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "insrt"]
               /\ UNCHANGED << table, secondary, newsecondary, P, evict, numEv, 
                               history, stack, outer, inner, fp, index, 
                               freePos, result, expectedEv, expected1, 
                               expected2 >>

insrt(self) == /\ pc[self] = "insrt"
               /\ IF index[self] < L
                     THEN /\ expected1' = [expected1 EXCEPT ![self] = table[idx(fp[self],index[self])]]
                          /\ IF expected1'[self] = empty \/ (expected1'[self] < 0 /\ expected1'[self] # (-1) * fp[self])
                                THEN /\ pc' = [pc EXCEPT ![self] = "incP"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "isMth"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "tryEv"]
                          /\ UNCHANGED expected1
               /\ UNCHANGED << table, secondary, newsecondary, P, evict, numEv, 
                               history, stack, outer, inner, fp, index, 
                               freePos, result, expectedEv, expected2 >>

isMth(self) == /\ pc[self] = "isMth"
               /\ IF isMatch(fp[self],idx(fp[self],index[self]),table)
                     THEN /\ pc' = [pc EXCEPT ![self] = "pick"]
                          /\ index' = index
                     ELSE /\ index' = [index EXCEPT ![self] = index[self] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "insrt"]
               /\ UNCHANGED << table, secondary, newsecondary, P, evict, numEv, 
                               history, stack, outer, inner, fp, freePos, 
                               result, expectedEv, expected1, expected2 >>

incP(self) == /\ pc[self] = "incP"
              /\ IF index[self] > P
                    THEN /\ P' = index[self]
                    ELSE /\ TRUE
                         /\ P' = P
              /\ pc' = [pc EXCEPT ![self] = "cas"]
              /\ UNCHANGED << table, secondary, newsecondary, evict, numEv, 
                              history, stack, outer, inner, fp, index, freePos, 
                              result, expectedEv, expected1, expected2 >>

cas(self) == /\ pc[self] = "cas"
             /\ IF numEv = expectedEv[self] /\ evict = FALSE /\ table[(idx(fp[self],index[self]))] = expected1[self]
                   THEN /\ table' = [table EXCEPT ![(idx(fp[self],index[self]))] = fp[self]]
                        /\ result' = [result EXCEPT ![self] = TRUE]
                   ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                        /\ table' = table
             /\ IF result'[self]
                   THEN /\ history' = (history \cup {fp[self]})
                        /\ pc' = [pc EXCEPT ![self] = "pick"]
                   ELSE /\ IF numEv > expectedEv[self] \/ evict
                              THEN /\ ~evict
                                   /\ pc' = [pc EXCEPT ![self] = "put"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "insrt"]
                        /\ UNCHANGED history
             /\ UNCHANGED << secondary, newsecondary, P, evict, numEv, stack, 
                             outer, inner, fp, index, freePos, expectedEv, 
                             expected1, expected2 >>

tryEv(self) == /\ pc[self] = "tryEv"
               /\ IF evict = FALSE
                     THEN /\ evict' = ~evict
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Evict",
                                                                   pc        |->  "endEv",
                                                                   outer     |->  outer[self],
                                                                   inner     |->  inner[self] ] >>
                                                               \o stack[self]]
                          /\ outer' = [outer EXCEPT ![self] = 1]
                          /\ inner' = [inner EXCEPT ![self] = 1]
                          /\ pc' = [pc EXCEPT ![self] = "strEv"]
                     ELSE /\ ~evict
                          /\ pc' = [pc EXCEPT ![self] = "put"]
                          /\ UNCHANGED << evict, stack, outer, inner >>
               /\ UNCHANGED << table, secondary, newsecondary, P, numEv, 
                               history, fp, index, freePos, result, expectedEv, 
                               expected1, expected2 >>

endEv(self) == /\ pc[self] = "endEv"
               /\ evict' = ~evict
               /\ numEv' = numEv + 1
               /\ pc' = [pc EXCEPT ![self] = "put"]
               /\ UNCHANGED << table, secondary, newsecondary, P, history, 
                               stack, outer, inner, fp, index, freePos, result, 
                               expectedEv, expected1, expected2 >>

p(self) == pick(self) \/ put(self) \/ cntns(self) \/ onSnc(self)
              \/ insrt(self) \/ isMth(self) \/ incP(self) \/ cas(self)
              \/ tryEv(self) \/ endEv(self)

Next == (\E self \in ProcSet: Evict(self))
           \/ (\E self \in Procs: p(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in Procs : WF_vars(p(self)) /\ WF_vars(Evict(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

(***************************************************************************)
(* A type correctness invariant for outer, inner and P.                    *)
(***************************************************************************)
TypeOK == /\ P \in Nat
          /\ P <= L
                        
(***************************************************************************)
(* All fingerprint in history are (always) hash table members,             *)
(* all fps \ history never are.                                            *)
(***************************************************************************)
Inv == /\ \A seen \in history: contains(seen,table,secondary,P+1)
       /\ \A unseen \in (fps \ history): ~contains(unseen,table,secondary,P+1)
       
(***************************************************************************)
(* FALSE iff table contains duplicate elements (excluding empty).          *)
(***************************************************************************)
Duplicates == LET sub == SelectSeq(table, LAMBDA e: e # empty)
              IN IF Len(sub) < 2 THEN TRUE
                 ELSE \A i \in 1..(Len(sub) - 1):
                                 /\ sub[i] # sub[i+1]
                                 /\ sub[i] # (-1) * sub[i+1]
                        
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
(* TRUE iff the maximum displacement of all elements # empty equal P. In   *)
(* other words, P is always minimal.                                       *)
(***************************************************************************)
Minimal == \A i \in 1..Len(table): IF table[i] = empty 
                                     THEN TRUE
                                     ELSE LET f == IF table[i] < 0 
                                                   THEN -1 * table[i]
                                                   ELSE table[i]
                                          IN (i - idx(f, 0)) <= P

(***************************************************************************)
(* P has to reach the limit L in some behaviors.                           *)
(***************************************************************************)
Maxed == <>(P = L)

(***************************************************************************)
(* Eventually, an eviction ends.                                           *)
(***************************************************************************)
EvictEnds == evict = TRUE ~> evict = FALSE

(***************************************************************************)
(* Under all behaviors, the algorithm makes progress.                      *)
(***************************************************************************)
Prop == <>[](history = fps)
=============================================================================
\end{tla}
