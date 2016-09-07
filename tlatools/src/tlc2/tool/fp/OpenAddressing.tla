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
(* TRUE iff the table at position index is empty.                          *)
(***************************************************************************)
isEmpty(index, table) == table[index] = empty

(***************************************************************************)
(* TRUE iff the table at position index is marked evicted.                 *)
(***************************************************************************)
isMarked(index, table) == table[index] < 0

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
(* actual index is lower than its primary idx. Another mental picture for  *)
(* table is a circular list and wrapped means that a fingerprint crossed   *)
(* the logically first position of table.                                  *) 
(***************************************************************************)
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
           P = 0,         \* AtomicInteger in Java
           evict = FALSE, \* AtomicBoolean in Java
           waitCnt = 0,   \* CyclicBarrier in Java
           history = {};
    
   (************************************************************************)
   (* Compare-and-swap is linearizable (appears atomic from the POV of     *)
   (* observers such as other threads) and disjoint-access-parallel (two   *)
   (* CAS operations on disjoint memory locations do not synchronize).     *)
   (*                                                                      *)
   (* Variants of CAS (only basic CAS supported by Java. No HW support     *)
   (* for DCAS, CASN):                                                     *)       
   (* CAS: Basic compare and swap of a 64bit memory location.              *)
   (* DWCAS: CAS of two adjacent/contigious 64bit memory locations.        *)
   (*        (CMPXCHG16) (to swap to adjacent positions in e.g table)      *)
   (* DCAS: CAS of two arbitrary 64bit memory locations (swap of arbitrary *)
   (*       locations).                                                    *)
   (* CASN: CAS N arbitrary 64bit memory locations.                        *)
   (*                                                                      *)
   (* http://liblfds.org/mediawiki/index.php?title=Article:CAS_and_LL/     *)
   (* SC_Implementation_Details_by_Processor_family                        *)       
   (************************************************************************)

   (* Atomically compare and swap. *)      
   macro CAS(result, pos, expected, new) {
     if (table[pos] = expected) {
         table[pos] := new;
          result := TRUE
     } else { 
          result := FALSE
     }
  }

  (* Eviction procedure. Runs in O(n), more precisely O(n * P) where P << n. *)
  procedure Evict()
     variables outer = 1, inner = 1, lo = 0, hi = 0; {
                (* For every element with index i in ascending order of table, sort the *)
                (* elements in the range i..i+P. The range can be seen as a lookahead. *)
     strEv:     while (outer+inner <= K+(2*(P+1))) {
                  lo := table[mod(outer, K)];
     read:        hi := table[mod(outer+inner, K)];
                  if (lo # empty /\ hi # empty /\ \* The model value empty # 0 which is why we check both
                      lo > 0 /\ hi > 0 /\
                      compare(lo,outer,hi,inner, P)) {
                      \* This is modelled as an atomic step in PlusCal
                      \* to always satisfy Inv. An implementation 
                      \* however need not do this atomic as all writers
                      \* are known to be suspended during Evict.
     swpLo :          table[mod(outer, K)] := hi ||
   (*swpHi:*)         table[mod(outer+inner, K)] := lo;
                  };
     incVr:       if (inner + 1 > P) {
                     (* Write table[mod(cpy,table)] to secondary. *)
     swpEv:          lo := table[mod(outer, K)];
                     if (lo # empty /\
                         lo > largestElem(newsecondary) /\
                         ((outer <= K /\ ~wrapped(lo,outer,P)) \/ 
                          (outer > K /\ wrapped(lo,outer,P)))) {
                        (* Copy all smaller fps than lo from secondary to newsecondary. *)
                        newsecondary := Append(newsecondary \o subSetSmaller(secondary, newsecondary, lo), lo);
                        (* Mark table[mod(cpy,table)] as being written to secondary. *)
                        table[mod(outer, K)] := lo * (-1);
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
  
  process (reader = "q") 
    variables rfp = 0, rindex = 0, checked = {}; {
     rwait:   await history # {};
     rpick:   while (TRUE) {
                  if (checked = history /\ history = fps) {
                     goto Done;
                  } else {
                     with (f \in history) { 
                        rfp := f;
                        checked := checked \cup {f};
                     };
                  };
                   
     rcntns:      rindex := 0;
                  if (evict) {
                     waitCnt := waitCnt + 1;
     rwaitEv:        await evict = FALSE;
     rendWEv:        waitCnt := waitCnt - 1;
                     goto rcntns
                  };
                 
     ronPrm:      while (rindex <= P) {
                     if (isMatch(rfp, idx(rfp, rindex), table)) {
                        goto rpick
                     } else {
                        if (isEmpty(idx(rfp, rindex), table) 
                         \/ isMarked(idx(rfp, rindex), table)) {
                           goto ronSnc;
                        } else {
                          rindex := rindex + 1
                        }
                     }
                  };
     ronSnc:      if (containsElem(secondary,rfp)) {
                      goto rpick
                  } else {
                      \* Since we picked a fp from history, it always 
                      \* either has to be in table or secondary.
                      assert(FALSE);
                  };
             }
  }
       
  (* A weak fair process. *)        
  fair process (p \in Procs)
    variables fp = 0,
              index = 0, 
              result = FALSE,
              expected = -1;
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
              result := FALSE;
              expected := -1;
              \* Wait for eviction thread to do its work.
              if (evict) {
                 waitCnt := waitCnt + 1;
     waitEv:     await evict = FALSE;
     endWEv:     waitCnt := waitCnt - 1;
                 goto put
              };
              
     chkSnc:  if (secondary # <<>>) {
                 (* Primary lookup. *)
     cntns:       while (index < P) {
                    if (isMatch(fp, idx(fp, index), table)) {
                       goto pick
                    } else {
                        if (isEmpty(idx(fp, index), table) 
                         \/ isMarked(idx(fp, index), table)) {
                            goto onSnc;
                        } else {
                            index := index + 1
                        }
                    }
                  };
              
              
                  (* Secondary lookup. *)
     onSnc:       if (containsElem(secondary,fp)) {
                     goto pick
                  } else {
                     \* Reset index to 0 after cntns for insrt to start
                     \* trying from position 0. Other threads might have
                     \* inserted fp in between cntns and insrt.
                     index := 0;
                  };
              };
              
              (* Put inserts the given fp into the hash table by sequentially trying *)
              (* the primary to the P's alternate position.                          *)
     insrt:   while (index < L) {
                 expected := table[idx(fp,index)];
                 if (expected = empty \/ (expected < 0 /\ expected # (-1) * fp))  {
     incP:           if (index > P) {P := index};
     cas:            CAS(result, idx(fp,index), expected, fp);
                     if (result) {
                        history := history \cup {fp};
                        goto pick
                     } else {
                        \* Has been occupied in the meantime,
                        \* try to find another position.
                        goto insrt
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
     tryEv:   if (evict = FALSE) {
                 evict := TRUE;
                 \* Wait for all other insertion threads and the one 
                 \* reader to park.
     waitIns:    await waitCnt = Cardinality(Procs) - 1 + 1;
                 call Evict();
     endEv:      evict := FALSE;
                 goto put;                   
               } else {
                 goto put
               }
             } 
           }
    }
}
***     this ends the comment containg the pluscal code      **********)
\* BEGIN TRANSLATION
VARIABLES table, secondary, newsecondary, P, evict, waitCnt, history, pc, 
          stack, outer, inner, lo, hi, rfp, rindex, checked, fp, index, 
          result, expected

vars == << table, secondary, newsecondary, P, evict, waitCnt, history, pc, 
           stack, outer, inner, lo, hi, rfp, rindex, checked, fp, index, 
           result, expected >>

ProcSet == {"q"} \cup (Procs)

Init == (* Global variables *)
        /\ table = [i \in 1..K |-> empty]
        /\ secondary = <<>>
        /\ newsecondary = <<>>
        /\ P = 0
        /\ evict = FALSE
        /\ waitCnt = 0
        /\ history = {}
        (* Procedure Evict *)
        /\ outer = [ self \in ProcSet |-> 1]
        /\ inner = [ self \in ProcSet |-> 1]
        /\ lo = [ self \in ProcSet |-> 0]
        /\ hi = [ self \in ProcSet |-> 0]
        (* Process reader *)
        /\ rfp = 0
        /\ rindex = 0
        /\ checked = {}
        (* Process p *)
        /\ fp = [self \in Procs |-> 0]
        /\ index = [self \in Procs |-> 0]
        /\ result = [self \in Procs |-> FALSE]
        /\ expected = [self \in Procs |-> -1]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "q" -> "rwait"
                                        [] self \in Procs -> "pick"]

strEv(self) == /\ pc[self] = "strEv"
               /\ IF outer[self]+inner[self] <= K+(2*(P+1))
                     THEN /\ lo' = [lo EXCEPT ![self] = table[mod(outer[self], K)]]
                          /\ pc' = [pc EXCEPT ![self] = "read"]
                          /\ UNCHANGED << secondary, newsecondary >>
                     ELSE /\ secondary' = newsecondary \o subSetLarger(secondary, newsecondary)
                          /\ newsecondary' = <<>>
                          /\ pc' = [pc EXCEPT ![self] = "rtrn"]
                          /\ lo' = lo
               /\ UNCHANGED << table, P, evict, waitCnt, history, stack, outer, 
                               inner, hi, rfp, rindex, checked, fp, index, 
                               result, expected >>

read(self) == /\ pc[self] = "read"
              /\ hi' = [hi EXCEPT ![self] = table[mod(outer[self]+inner[self], K)]]
              /\ IF lo[self] # empty /\ hi'[self] # empty /\
                    lo[self] > 0 /\ hi'[self] > 0 /\
                    compare(lo[self],outer[self],hi'[self],inner[self], P)
                    THEN /\ pc' = [pc EXCEPT ![self] = "swpLo"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "incVr"]
              /\ UNCHANGED << table, secondary, newsecondary, P, evict, 
                              waitCnt, history, stack, outer, inner, lo, rfp, 
                              rindex, checked, fp, index, result, expected >>

swpLo(self) == /\ pc[self] = "swpLo"
               /\ table' = [table EXCEPT ![mod(outer[self], K)] = hi[self],
                                         ![mod(outer[self]+inner[self], K)] = lo[self]]
               /\ pc' = [pc EXCEPT ![self] = "incVr"]
               /\ UNCHANGED << secondary, newsecondary, P, evict, waitCnt, 
                               history, stack, outer, inner, lo, hi, rfp, 
                               rindex, checked, fp, index, result, expected >>

incVr(self) == /\ pc[self] = "incVr"
               /\ IF inner[self] + 1 > P
                     THEN /\ pc' = [pc EXCEPT ![self] = "swpEv"]
                          /\ inner' = inner
                     ELSE /\ inner' = [inner EXCEPT ![self] = inner[self] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "strEv"]
               /\ UNCHANGED << table, secondary, newsecondary, P, evict, 
                               waitCnt, history, stack, outer, lo, hi, rfp, 
                               rindex, checked, fp, index, result, expected >>

swpEv(self) == /\ pc[self] = "swpEv"
               /\ lo' = [lo EXCEPT ![self] = table[mod(outer[self], K)]]
               /\ IF lo'[self] # empty /\
                     lo'[self] > largestElem(newsecondary) /\
                     ((outer[self] <= K /\ ~wrapped(lo'[self],outer[self],P)) \/
                      (outer[self] > K /\ wrapped(lo'[self],outer[self],P)))
                     THEN /\ newsecondary' = Append(newsecondary \o subSetSmaller(secondary, newsecondary, lo'[self]), lo'[self])
                          /\ table' = [table EXCEPT ![mod(outer[self], K)] = lo'[self] * (-1)]
                     ELSE /\ TRUE
                          /\ UNCHANGED << table, newsecondary >>
               /\ inner' = [inner EXCEPT ![self] = 1]
               /\ outer' = [outer EXCEPT ![self] = outer[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "strEv"]
               /\ UNCHANGED << secondary, P, evict, waitCnt, history, stack, 
                               hi, rfp, rindex, checked, fp, index, result, 
                               expected >>

rtrn(self) == /\ pc[self] = "rtrn"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ outer' = [outer EXCEPT ![self] = Head(stack[self]).outer]
              /\ inner' = [inner EXCEPT ![self] = Head(stack[self]).inner]
              /\ lo' = [lo EXCEPT ![self] = Head(stack[self]).lo]
              /\ hi' = [hi EXCEPT ![self] = Head(stack[self]).hi]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << table, secondary, newsecondary, P, evict, 
                              waitCnt, history, rfp, rindex, checked, fp, 
                              index, result, expected >>

Evict(self) == strEv(self) \/ read(self) \/ swpLo(self) \/ incVr(self)
                  \/ swpEv(self) \/ rtrn(self)

rwait == /\ pc["q"] = "rwait"
         /\ history # {}
         /\ pc' = [pc EXCEPT !["q"] = "rpick"]
         /\ UNCHANGED << table, secondary, newsecondary, P, evict, waitCnt, 
                         history, stack, outer, inner, lo, hi, rfp, rindex, 
                         checked, fp, index, result, expected >>

rpick == /\ pc["q"] = "rpick"
         /\ IF checked = history /\ history = fps
               THEN /\ pc' = [pc EXCEPT !["q"] = "Done"]
                    /\ UNCHANGED << rfp, checked >>
               ELSE /\ \E f \in history:
                         /\ rfp' = f
                         /\ checked' = (checked \cup {f})
                    /\ pc' = [pc EXCEPT !["q"] = "rcntns"]
         /\ UNCHANGED << table, secondary, newsecondary, P, evict, waitCnt, 
                         history, stack, outer, inner, lo, hi, rindex, fp, 
                         index, result, expected >>

rcntns == /\ pc["q"] = "rcntns"
          /\ rindex' = 0
          /\ IF evict
                THEN /\ waitCnt' = waitCnt + 1
                     /\ pc' = [pc EXCEPT !["q"] = "rwaitEv"]
                ELSE /\ pc' = [pc EXCEPT !["q"] = "ronPrm"]
                     /\ UNCHANGED waitCnt
          /\ UNCHANGED << table, secondary, newsecondary, P, evict, history, 
                          stack, outer, inner, lo, hi, rfp, checked, fp, index, 
                          result, expected >>

rwaitEv == /\ pc["q"] = "rwaitEv"
           /\ evict = FALSE
           /\ pc' = [pc EXCEPT !["q"] = "rendWEv"]
           /\ UNCHANGED << table, secondary, newsecondary, P, evict, waitCnt, 
                           history, stack, outer, inner, lo, hi, rfp, rindex, 
                           checked, fp, index, result, expected >>

rendWEv == /\ pc["q"] = "rendWEv"
           /\ waitCnt' = waitCnt - 1
           /\ pc' = [pc EXCEPT !["q"] = "rcntns"]
           /\ UNCHANGED << table, secondary, newsecondary, P, evict, history, 
                           stack, outer, inner, lo, hi, rfp, rindex, checked, 
                           fp, index, result, expected >>

ronPrm == /\ pc["q"] = "ronPrm"
          /\ IF rindex <= P
                THEN /\ IF isMatch(rfp, idx(rfp, rindex), table)
                           THEN /\ pc' = [pc EXCEPT !["q"] = "rpick"]
                                /\ UNCHANGED rindex
                           ELSE /\ IF    isEmpty(idx(rfp, rindex), table)
                                      \/ isMarked(idx(rfp, rindex), table)
                                      THEN /\ pc' = [pc EXCEPT !["q"] = "ronSnc"]
                                           /\ UNCHANGED rindex
                                      ELSE /\ rindex' = rindex + 1
                                           /\ pc' = [pc EXCEPT !["q"] = "ronPrm"]
                ELSE /\ pc' = [pc EXCEPT !["q"] = "ronSnc"]
                     /\ UNCHANGED rindex
          /\ UNCHANGED << table, secondary, newsecondary, P, evict, waitCnt, 
                          history, stack, outer, inner, lo, hi, rfp, checked, 
                          fp, index, result, expected >>

ronSnc == /\ pc["q"] = "ronSnc"
          /\ IF containsElem(secondary,rfp)
                THEN /\ pc' = [pc EXCEPT !["q"] = "rpick"]
                ELSE /\ Assert((FALSE), 
                               "Failure of assertion at line 289, column 23.")
                     /\ pc' = [pc EXCEPT !["q"] = "rpick"]
          /\ UNCHANGED << table, secondary, newsecondary, P, evict, waitCnt, 
                          history, stack, outer, inner, lo, hi, rfp, rindex, 
                          checked, fp, index, result, expected >>

reader == rwait \/ rpick \/ rcntns \/ rwaitEv \/ rendWEv \/ ronPrm
             \/ ronSnc

pick(self) == /\ pc[self] = "pick"
              /\ IF (fps \ history) = {}
                    THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ fp' = fp
                    ELSE /\ \E f \in (fps \ history):
                              fp' = [fp EXCEPT ![self] = f]
                         /\ pc' = [pc EXCEPT ![self] = "put"]
              /\ UNCHANGED << table, secondary, newsecondary, P, evict, 
                              waitCnt, history, stack, outer, inner, lo, hi, 
                              rfp, rindex, checked, index, result, expected >>

put(self) == /\ pc[self] = "put"
             /\ index' = [index EXCEPT ![self] = 0]
             /\ result' = [result EXCEPT ![self] = FALSE]
             /\ expected' = [expected EXCEPT ![self] = -1]
             /\ IF evict
                   THEN /\ waitCnt' = waitCnt + 1
                        /\ pc' = [pc EXCEPT ![self] = "waitEv"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "chkSnc"]
                        /\ UNCHANGED waitCnt
             /\ UNCHANGED << table, secondary, newsecondary, P, evict, history, 
                             stack, outer, inner, lo, hi, rfp, rindex, checked, 
                             fp >>

waitEv(self) == /\ pc[self] = "waitEv"
                /\ evict = FALSE
                /\ pc' = [pc EXCEPT ![self] = "endWEv"]
                /\ UNCHANGED << table, secondary, newsecondary, P, evict, 
                                waitCnt, history, stack, outer, inner, lo, hi, 
                                rfp, rindex, checked, fp, index, result, 
                                expected >>

endWEv(self) == /\ pc[self] = "endWEv"
                /\ waitCnt' = waitCnt - 1
                /\ pc' = [pc EXCEPT ![self] = "put"]
                /\ UNCHANGED << table, secondary, newsecondary, P, evict, 
                                history, stack, outer, inner, lo, hi, rfp, 
                                rindex, checked, fp, index, result, expected >>

chkSnc(self) == /\ pc[self] = "chkSnc"
                /\ IF secondary # <<>>
                      THEN /\ pc' = [pc EXCEPT ![self] = "cntns"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "insrt"]
                /\ UNCHANGED << table, secondary, newsecondary, P, evict, 
                                waitCnt, history, stack, outer, inner, lo, hi, 
                                rfp, rindex, checked, fp, index, result, 
                                expected >>

cntns(self) == /\ pc[self] = "cntns"
               /\ IF index[self] < P
                     THEN /\ IF isMatch(fp[self], idx(fp[self], index[self]), table)
                                THEN /\ pc' = [pc EXCEPT ![self] = "pick"]
                                     /\ index' = index
                                ELSE /\ IF    isEmpty(idx(fp[self], index[self]), table)
                                           \/ isMarked(idx(fp[self], index[self]), table)
                                           THEN /\ pc' = [pc EXCEPT ![self] = "onSnc"]
                                                /\ index' = index
                                           ELSE /\ index' = [index EXCEPT ![self] = index[self] + 1]
                                                /\ pc' = [pc EXCEPT ![self] = "cntns"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "onSnc"]
                          /\ index' = index
               /\ UNCHANGED << table, secondary, newsecondary, P, evict, 
                               waitCnt, history, stack, outer, inner, lo, hi, 
                               rfp, rindex, checked, fp, result, expected >>

onSnc(self) == /\ pc[self] = "onSnc"
               /\ IF containsElem(secondary,fp[self])
                     THEN /\ pc' = [pc EXCEPT ![self] = "pick"]
                          /\ index' = index
                     ELSE /\ index' = [index EXCEPT ![self] = 0]
                          /\ pc' = [pc EXCEPT ![self] = "insrt"]
               /\ UNCHANGED << table, secondary, newsecondary, P, evict, 
                               waitCnt, history, stack, outer, inner, lo, hi, 
                               rfp, rindex, checked, fp, result, expected >>

insrt(self) == /\ pc[self] = "insrt"
               /\ IF index[self] < L
                     THEN /\ expected' = [expected EXCEPT ![self] = table[idx(fp[self],index[self])]]
                          /\ IF expected'[self] = empty \/ (expected'[self] < 0 /\ expected'[self] # (-1) * fp[self])
                                THEN /\ pc' = [pc EXCEPT ![self] = "incP"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "isMth"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "tryEv"]
                          /\ UNCHANGED expected
               /\ UNCHANGED << table, secondary, newsecondary, P, evict, 
                               waitCnt, history, stack, outer, inner, lo, hi, 
                               rfp, rindex, checked, fp, index, result >>

isMth(self) == /\ pc[self] = "isMth"
               /\ IF isMatch(fp[self],idx(fp[self],index[self]),table)
                     THEN /\ pc' = [pc EXCEPT ![self] = "pick"]
                          /\ index' = index
                     ELSE /\ index' = [index EXCEPT ![self] = index[self] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "insrt"]
               /\ UNCHANGED << table, secondary, newsecondary, P, evict, 
                               waitCnt, history, stack, outer, inner, lo, hi, 
                               rfp, rindex, checked, fp, result, expected >>

incP(self) == /\ pc[self] = "incP"
              /\ IF index[self] > P
                    THEN /\ P' = index[self]
                    ELSE /\ TRUE
                         /\ P' = P
              /\ pc' = [pc EXCEPT ![self] = "cas"]
              /\ UNCHANGED << table, secondary, newsecondary, evict, waitCnt, 
                              history, stack, outer, inner, lo, hi, rfp, 
                              rindex, checked, fp, index, result, expected >>

cas(self) == /\ pc[self] = "cas"
             /\ IF table[(idx(fp[self],index[self]))] = expected[self]
                   THEN /\ table' = [table EXCEPT ![(idx(fp[self],index[self]))] = fp[self]]
                        /\ result' = [result EXCEPT ![self] = TRUE]
                   ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                        /\ table' = table
             /\ IF result'[self]
                   THEN /\ history' = (history \cup {fp[self]})
                        /\ pc' = [pc EXCEPT ![self] = "pick"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "insrt"]
                        /\ UNCHANGED history
             /\ UNCHANGED << secondary, newsecondary, P, evict, waitCnt, stack, 
                             outer, inner, lo, hi, rfp, rindex, checked, fp, 
                             index, expected >>

tryEv(self) == /\ pc[self] = "tryEv"
               /\ IF evict = FALSE
                     THEN /\ evict' = TRUE
                          /\ pc' = [pc EXCEPT ![self] = "waitIns"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "put"]
                          /\ evict' = evict
               /\ UNCHANGED << table, secondary, newsecondary, P, waitCnt, 
                               history, stack, outer, inner, lo, hi, rfp, 
                               rindex, checked, fp, index, result, expected >>

waitIns(self) == /\ pc[self] = "waitIns"
                 /\ waitCnt = Cardinality(Procs) - 1 + 1
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Evict",
                                                          pc        |->  "endEv",
                                                          outer     |->  outer[self],
                                                          inner     |->  inner[self],
                                                          lo        |->  lo[self],
                                                          hi        |->  hi[self] ] >>
                                                      \o stack[self]]
                 /\ outer' = [outer EXCEPT ![self] = 1]
                 /\ inner' = [inner EXCEPT ![self] = 1]
                 /\ lo' = [lo EXCEPT ![self] = 0]
                 /\ hi' = [hi EXCEPT ![self] = 0]
                 /\ pc' = [pc EXCEPT ![self] = "strEv"]
                 /\ UNCHANGED << table, secondary, newsecondary, P, evict, 
                                 waitCnt, history, rfp, rindex, checked, fp, 
                                 index, result, expected >>

endEv(self) == /\ pc[self] = "endEv"
               /\ evict' = FALSE
               /\ pc' = [pc EXCEPT ![self] = "put"]
               /\ UNCHANGED << table, secondary, newsecondary, P, waitCnt, 
                               history, stack, outer, inner, lo, hi, rfp, 
                               rindex, checked, fp, index, result, expected >>

p(self) == pick(self) \/ put(self) \/ waitEv(self) \/ endWEv(self)
              \/ chkSnc(self) \/ cntns(self) \/ onSnc(self) \/ insrt(self)
              \/ isMth(self) \/ incP(self) \/ cas(self) \/ tryEv(self)
              \/ waitIns(self) \/ endEv(self)

Next == reader
           \/ (\E self \in ProcSet: Evict(self))
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

(***************************************************************************)
(* TRUE iff fingerprints correctly transition from table to newsecondary   *)
(* to secondary.                                                           *)
(***************************************************************************)
Consistent == \A seen \in history:
        /\ (containedInTable(seen) => ~containedInSecondary(seen))
        /\ (containedInTable(seen) => ~containedInNewSecondary(seen))
        /\ (~containedInTable(seen) => (containedInSecondary(seen)) \/ 
                                        containedInNewSecondary(seen))
        /\ (containedInTable(seen * (-1)) => (containedInSecondary(seen)) \/ 
                                              containedInNewSecondary(seen))
\* Universal quantification and leads-to not supported by TLC
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
(* Under all behaviors, the algorithm makes progress.                      *)
(***************************************************************************)
Prop == <>[](history = fps)
=============================================================================