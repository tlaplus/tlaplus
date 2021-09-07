\* Java implementation at ../OffHeapDiskFPSet.java or https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tlc2/tool/fp/OffHeapDiskFPSet.java

\begin{ppcal}
-------------------------- MODULE OpenAddressing --------------------------
EXTENDS Sequences, FiniteSets, Integers

(***************************************************************************)
(* K: The overall number of fingerprints that fit into the table.          *)
(* fps: The set of fingerprints to be inserted into the hash table.        *)
(* empty: An empty (model) value. Used to mark an unoccupied table element.*)
(* Writer: The set of processes/threads which insert fingerprints. Reader: *)
(* The set of processes which check fingerprints with contains. L: The     *)
(* probing limit.                                                          *)
(***************************************************************************)
CONSTANT K, fps, empty, Writer, Reader, L

(***************************************************************************)
(* K is a positive natural.  emtpy is different from all elements in fps.  *)
(* fingerprints are natural numbers and can be well-ordered.               *)
(***************************************************************************)
ASSUME /\ K \in (Nat \ {0})
       /\ \A fp \in fps: fp \in (Nat \ {0})
       /\ empty \notin fps
       /\ (2*L) <= K 

----------------------------------------------------------------------------

(***************************************************************************)
(* The image of the function F.                                            *)
(***************************************************************************)
Image(F) == { F[x] : x \in DOMAIN F }

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
subSeqSmaller(seq1, seq2, elem) == SelectSeq(seq1, LAMBDA p:
                                     p < elem /\ p > largestElem(seq2))               

(***************************************************************************)
(* All elements of seq1 larger than the largest element in seq2.           *)
(***************************************************************************)
subSeqLarger(seq1, seq2) == IF seq2 = <<>> 
                            THEN seq1 
                            ELSE SelectSeq(seq1, LAMBDA p:
                                                    p > largestElem(seq2))               

(***************************************************************************)
(* TRUE iff the sequence seq contains the element elem.                    *)
(***************************************************************************)
containsElem(seq, elem) == elem \in Image(seq)
                    
(***************************************************************************)
(* The minimum and maximum element in set S.                               *)
(***************************************************************************)
min(S) == CHOOSE s \in S: \A a \in S: s <= a 
max(S) == CHOOSE s \in S: \A a \in S: s >= a 
                     
(***************************************************************************)
(* The smaller of the two values.                                          *)
(***************************************************************************)
minimum(a, b) == IF a < b THEN a ELSE b
                     
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
(* such that: p \in 0..L.                                                  *)
(***************************************************************************)
idx(fp, p) == rescale(K, max(fps), min(fps), fp, p)

(***************************************************************************)
(* TRUE iff the fingerprint at table position index is equal to fp or its  *)
(* corresponding negative fp value (marked as to be copied to external).   *)
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

----------------------------------------------------------------------------

(***************************************************************************)
(* A fp wrapped around if its alternate indices are beyond K and its       *)
(* actual index is lower than its primary idx. Another mental picture for  *)
(* table is a circular list and wrapped means that a fingerprint crossed   *)
(* the logically first position of table.                                  *) 
(***************************************************************************)
wrapped(fp, pos) == idx(fp, 0) > mod(pos, K) 

(***************************************************************************)
(* Compare the two fingerprints fp1 and fp2 for order with regards to      *) 
(* their numerical values and their respective positions i1 and i2.        *)
(*                                                                         *)
(* Returns -1, iff fp2 is less than fp1. Returns 0, iff fp1 and fp2 are    *)
(* equal. Returns 1, iff fp1 is less than fp2.                             *)
(*                                                                         *)
(* compare considers three cases:                                          *)
(* 1) Iff either one or both fingerprints are empty, they are defined to   *)
(*    be equal. Under the assumption of a stable sorting algorithm, fp1    *)
(*    and fp2 are not swapped (ELSE 0).                                    *)
(* 2) Iff neither one or both fingerprints wrapped, a basic comparison is  *)
(*    done. A basic comparison is one, where the lower positioned fp has   *)
(*    to be numerically lower.                                             *)
(* 3) Iff the truth values for wrapped differed, two cases have to be      *)
(*    distinguished:                                                       *)
(*                                                                         *)
(*     Let:                                                                *)
(*     $\overset{\circlearrowleft}{fps} \triangleq {fp \in fps:            *)
(*               \E i \in Image(PS[fp]): wrapped(fp,i)}$                   *)
(*                                                                         *)
(*     $\overrightarrow{fps} \triangleq fps \                              *)
(*                        \overset{\circlearrowleft}{fps}$                 *)
(*                                                                         *)
(* 3a) Comparison when fp1 and fp2 are both in                             *)
(*     $\overset{\circlearrowleft}{fps}$. If fp1 is at a lower             *)
(*     position (thus wrapped) and numerically lower, swap it with fp2     *)
(*     which is at a higher position and thus did not wrap.                *)
(*     For example, fp1 was inserted into the table after fp2 and thus     *)
(*     wrapped, but is numerically lower than fp2.                         *)
(*                                                                         *)
(* 3b) Special case comparison required by Insertion Sort. It compares a   *)
(*     fingerprint in $\overset{\circlearrowleft}{fps}$ with one in        *) 
(*     $\overrightarrow{fps}$.                                             *)
(*     Insertion Sort compares adjacent elements. Thus, without this case  *)
(*     two fingerprints fp1 and fpX, which are eventually handled by 3a),  *)
(*     would not be sorted, iff fp2 is inbetween of fp1 and fpX. Thus, fp1 *)
(*     is swapped with fp2 meaning it moves towards the beginning of table.*)
(*     Eventually, all wrapped fingerprints in                             *)
(*     $\overset{\circlearrowleft}{fps}$ will form a cluster               *)
(*     at the beginning of t and can then be sorted with 3a). In other     *)
(*     words, we allow the wrapped fingerprints to be compacted at the     *)
(*     beginning ot the table and non-wrapping fingerprints to be moved to *)
(*     higher positions.                                                   *)
(*                                                                         *)
(*     Assumeming that the beginning of table is:                          *)
(*     <<1,23,22,...,24>> (assuming fps is 1..24, L=3 and K=6. Sorted,     *)
(*     table needs to change to <<1,23,24,...,22>>.                        *)
(*     Without 3b), Insertion Sort compares 22 to 1 and 23 to 22. The      *)
(*     outcome would be <<1,22,23,...,24>>, which is cleary not fully      *)
(*     sorted. Thus, in order to handle this case, we allow IS to swap 22  *)
(*     and 23 with 1. As a result, table - when sorted - is                *)
(*     <<23,24,1,...,22>>.                                                 *)
(*                                                                         *)
(*     Can we be sure, that non-wrapping fingerprints do not get moved out *)
(*     beyond the end of their probing sequence?                           *)
(*     Obvously, at most, L-1 wrapping fingerprints can be located at the  *)
(*     beginning of table. In this case, only one non-wrapping fingerprint *)
(*     will be in the table, which maximally will be moved L-1 positions   *)
(*     to the right with regards to its primary position.                  *)
(***************************************************************************)
compare(fp1,i1,fp2,i2) == 
                IF fp1 \in fps /\ fp2 \in fps                         \* 1)
                THEN IF wrapped(fp1, i1) = wrapped(fp2, i2)           \* 2)
                     THEN IF i1 > i2 /\ fp1 < fp2 THEN -1 ELSE 1
                     ELSE IF i1 < i2 /\ fp1 < fp2 THEN -1 ELSE        \* 3a
                          IF i1 > i2 /\ fp1 > fp2 THEN -1 ELSE 0      \* 3b
                ELSE 0            
                             
----------------------------------------------------------------------------

(***       this is a comment containing the PlusCal code *
--algorithm OpenAddressing 
(***************************************************************************)
(* table: The actual hash table specified as a TLA+ sequence. history: An  *)
(* auxiliary (history) variable unrelated to the actual hash table         *)
(* specification. It just records the inserted fingerprints to be verified *)
(* by Inv. An implementation won't need history. external: The external  *)
(* storage where fingerprints are eventually evicted to. outer/inner:      *)
(* Index variables local to the sort action. L: The number of times an     *) 
(* alternate index is to be tried.                                         *)          
(***************************************************************************)
{ variable table = [i \in 1..K |-> empty], 
           external = <<>>,
           newexternal = <<>>,
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
   (* DWCAS: CAS of two adjacent/contiguous 64bit memory locations.        *)
   (*        (CMPXCHG16) (to swap to adjacent positions in e.g table)      *)
   (* DCAS: CAS of two arbitrary 64bit memory locations (swap of arbitrary *)
   (*       locations).                                                    *)
   (* CASN: CAS N arbitrary 64bit memory locations.                        *)
   (*                                                                      *)
   (* http://liblfds.org/mediawiki/index.php?title=Article:CAS_and_LL/     *)
   (* SC_Implementation_Details_by_Processor_family                        *)       
   (************************************************************************)

  (* Atomically compare and swap an element of table.    *)
  (* Atomicity is implicit due to the absence of labels. *)      
  macro CAS(result, pos, expected, new) {
     if (table[pos] = expected) {
         table[pos] := new;
         result := TRUE
     } else { 
         result := FALSE
     }
  }

  procedure Evict()
     variables ei = 1, ej = 1, lo = 0; {
                (* Insertion sort. *)
     strIns:    while (ei <= K+L) {
                  lo := table[mod(ei + 1, K)];
     nestedIns:   while (compare(lo, mod(ei + 1, K), 
                            table[mod(ej, K)], mod(ej, K)) <= -1) {
                    table[mod(ej + 1, K)] := table[mod(ej, K)];
                    if (ej = 0) {
                       ej := ej - 1;
                       goto set;
                    } else {
                       ej := ej - 1;
                    };
                  };
     set:         table[mod(ej + 1, K)] := lo;
                  ej := ei + 1;
                  ei := ei + 1;
                };
                ei := 1;
                
                (* Write to external storage. *)
     flush:     while (ei <= K+L) {
                     lo := table[mod(ei, K)];
                     if (lo # empty /\
                         lo > largestElem(newexternal) /\
                         ((ei <= K /\ ~wrapped(lo,ei)) \/ 
                          (ei > K /\ wrapped(lo,ei)))) {
                        (* Copy all smaller fps than lo from   *)
                        (* secondary to newexternal.          *)
                        newexternal := Append(newexternal \o 
                               subSeqSmaller(external, newexternal, lo), lo);
                        (* Mark table[mod(cpy,table)] as being *)
                        (* written to external.               *)
                        table[mod(ei, K)] := lo * (-1);
                     };
                     ei := ei + 1;
                };
                (* Append remainder of external to newexternal and *) 
                (* assign newexternal to external. *)
                external := newexternal \o 
                             subSeqLarger(external, newexternal);
                newexternal := <<>>;
     rtrn:      return;
  }
  
\*  process (q \in Reader) 
\*    variables rfp = 0, rindex = 0, checked = {}; {
\*     rwait:   await history # {};
\*     rpick:   while (TRUE) {
\*                  if (checked = history /\ history = fps) {
\*                     goto Done;
\*                  } else {
\*                     with (f \in history) { 
\*                        rfp := f;
\*                        checked := checked \cup {f};
\*                     };
\*                  };
\*                   
\*     rcntns:      rindex := 0;
\*                  if (evict) {
\*                     waitCnt := waitCnt + 1;
\*     rwaitEv:        await evict = FALSE;
\*     rendWEv:        waitCnt := waitCnt - 1;
\*                     goto rcntns
\*                  };
\*                 
\*     ronPrm:      while (rindex <= L) {
\*                     if (isMatch(rfp, idx(rfp, rindex), table)) {
\*                        goto rpick
\*                     } else {
\*                        if (isEmpty(idx(rfp, rindex), table) 
\*                         \/ isMarked(idx(rfp, rindex), table)) {
\*                           goto ronSnc;
\*                        } else {
\*                          rindex := rindex + 1
\*                        }
\*                     }
\*                  };
\*     ronSnc:      if (containsElem(external,rfp)) {
\*                      goto rpick
\*                  } else {
\*                      (* Since we picked a fp from history, it always *) 
\*                      (* either has to be in table or external.      *)
\*                      assert(FALSE);
\*                  };
\*             }
\*  }
       
  (* A weak fair process. *)        
  fair process (p \in Writer)
    variables fp = 0, index = 0, result = FALSE, expected = -1; {
    pick:  while (TRUE) {
              (* No deadlock once all fingerprints have been inserted. *)
              if ((fps \ history) = {}) {
                goto Done;
              } else {
                (* Select some fp to be inserted *)
                with (f \in (fps \ history)) { fp := f; };
              };

     put:     index := 0;
              result := FALSE;
              (* Set expected to infinity. expected is reused when  *)
              (* the algorithm runs a primary lookup and finds a    *)
              (* position which is either EMPTY or isMarked(...).   *)
              (* expected stores the (open) position for later use  *)
              (* where the fp is inserted. Maximally, a position    *)
              (* can be K + L, thus expected is set to K + L + 1;   *)
              (* as an approximation of infinity.                   *)
              expected := L;
              (* Wait for eviction thread to do its work. *)
              if (evict) {
                 waitCnt := waitCnt + 1;
     waitEv:     await evict = FALSE;
     endWEv:     waitCnt := waitCnt - 1;
                 goto put
              };
              
              (* Check external unless empty. First though, we do    *)
              (* a primary lookup in case the fp in question has not *)
              (* been evicted to external yet.                       *)
     chkSnc:  if (external # <<>>) {
                 (* Primary lookup. *)
     cntns:       while (index < L) {
                    if (isMatch(fp, idx(fp, index), table)) {
                       goto pick
                    } else {
                        if (isEmpty(idx(fp, index), table)) {
                            (* Found an EMPTY position which proves *) 
                            (* that fp cannot be found at higher    *)
                            (* positions. Thus, no need to continue.*)
                            expected := minimum(expected, index);
                            goto onSnc;
                        } else {
                            if (isMarked(idx(fp, index), table)) {
                                (* None of the lower positions has    *)
                                (* fp, thus keep the lowest position  *)
                                (* for the second loop as the start   *)
                                (* index. No point in checking known  *)
                                (* lower positions in the loop again. *)                                
                                expected := minimum(expected, index);
                                index := index + 1;
                            } else {
                                index := index + 1
                            }
                        }
                    }
                  };
              
              
                  (* External lookup. *)
     onSnc:       if (containsElem(external,fp)) {
                     goto pick
                  } else {
                     (* Have next loop start at expected determined *)
                     (* by previous loop.                           *)
                     index := expected;
                     (* Re-init expected to be used for its alternate purpose. *)
                     expected := -1;
                  };
              };
              
              (* Put inserts the given fp into the hash table by sequentially *)
              (* trying the primary to the L's alternate position.            *)
     insrt:   while (index < L) {
                 expected := table[idx(fp,index)];
                 if (expected = empty \/ 
                     (expected < 0 /\ expected # (-1) * fp))  {
     cas:            CAS(result, idx(fp,index), expected, fp);
                     if (result) {
                        history := history \cup {fp};
                        goto pick
                     } else {
                        (* Has been occupied in the meantime, *)
                        (* try to find another position.      *)
                        goto insrt
                      }
                 };
                
                 (* Has fp been inserted by another process? Check isMatch *)
                 (* AFTER empty and on-external because of two reasons:    *)
                 (* a) Thread A finds table[pos] to be empty but fails     *)
                 (*    to CAS fpX. Thread B concurrently also finds        *)
                 (*    table[pos] to be empty and succeeds to CAS fpX.     *)
                 (* b) Iff table[pos] is empty or -1, higher positions     *)
                 (*    cannot be a match.                                  *)
     isMth:      if (isMatch(fp,idx(fp,index),table)) {
                    goto pick
                 } else {
                    index := index + 1;
                 };
              }; \* end of while/insrt


              (* We failed to insert fp into a full table, thus try *)
              (* to become the thread that evicts to external.      *)
              (* The label tryEv makes sure, that the read and      *) 
              (* write occur atomically. An implementation has to   *)
              (* CAS or use some other mechanism to control         *)
              (* concurrency.                                       *)
     tryEv:   if (evict = FALSE) {
                 (* CAS evict! *)
                 evict := TRUE;
                 (* Wait for all other insertion threads and  *) 
                 (* the one reader to park.                   *)
     waitIns:    await waitCnt = Cardinality(Writer) - 1 + Cardinality(Reader);
                 call Evict();
     endEv:      evict := FALSE;
                 goto put;                   
              } else {
                 goto put
              }
            }
         } \* end while/pick
    }
}
***     this ends the comment containg the pluscal code      **********)
\* BEGIN TRANSLATION (chksum(pcal) = "b4d45dd9" /\ chksum(tla) = "7e9e5338")
VARIABLES table, external, newexternal, evict, waitCnt, history, pc, stack, 
          ei, ej, lo, fp, index, result, expected

vars == << table, external, newexternal, evict, waitCnt, history, pc, stack, 
           ei, ej, lo, fp, index, result, expected >>

ProcSet == (Writer)

Init == (* Global variables *)
        /\ table = [i \in 1..K |-> empty]
        /\ external = <<>>
        /\ newexternal = <<>>
        /\ evict = FALSE
        /\ waitCnt = 0
        /\ history = {}
        (* Procedure Evict *)
        /\ ei = [ self \in ProcSet |-> 1]
        /\ ej = [ self \in ProcSet |-> 1]
        /\ lo = [ self \in ProcSet |-> 0]
        (* Process p *)
        /\ fp = [self \in Writer |-> 0]
        /\ index = [self \in Writer |-> 0]
        /\ result = [self \in Writer |-> FALSE]
        /\ expected = [self \in Writer |-> -1]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "pick"]

strIns(self) == /\ pc[self] = "strIns"
                /\ IF ei[self] <= K+L
                      THEN /\ lo' = [lo EXCEPT ![self] = table[mod(ei[self] + 1, K)]]
                           /\ pc' = [pc EXCEPT ![self] = "nestedIns"]
                           /\ ei' = ei
                      ELSE /\ ei' = [ei EXCEPT ![self] = 1]
                           /\ pc' = [pc EXCEPT ![self] = "flush"]
                           /\ lo' = lo
                /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                                history, stack, ej, fp, index, result, 
                                expected >>

nestedIns(self) == /\ pc[self] = "nestedIns"
                   /\ IF compare(lo[self], mod(ei[self] + 1, K),
                            table[mod(ej[self], K)], mod(ej[self], K)) <= -1
                         THEN /\ table' = [table EXCEPT ![mod(ej[self] + 1, K)] = table[mod(ej[self], K)]]
                              /\ IF ej[self] = 0
                                    THEN /\ ej' = [ej EXCEPT ![self] = ej[self] - 1]
                                         /\ pc' = [pc EXCEPT ![self] = "set"]
                                    ELSE /\ ej' = [ej EXCEPT ![self] = ej[self] - 1]
                                         /\ pc' = [pc EXCEPT ![self] = "nestedIns"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "set"]
                              /\ UNCHANGED << table, ej >>
                   /\ UNCHANGED << external, newexternal, evict, waitCnt, 
                                   history, stack, ei, lo, fp, index, result, 
                                   expected >>

set(self) == /\ pc[self] = "set"
             /\ table' = [table EXCEPT ![mod(ej[self] + 1, K)] = lo[self]]
             /\ ej' = [ej EXCEPT ![self] = ei[self] + 1]
             /\ ei' = [ei EXCEPT ![self] = ei[self] + 1]
             /\ pc' = [pc EXCEPT ![self] = "strIns"]
             /\ UNCHANGED << external, newexternal, evict, waitCnt, history, 
                             stack, lo, fp, index, result, expected >>

flush(self) == /\ pc[self] = "flush"
               /\ IF ei[self] <= K+L
                     THEN /\ lo' = [lo EXCEPT ![self] = table[mod(ei[self], K)]]
                          /\ IF lo'[self] # empty /\
                                lo'[self] > largestElem(newexternal) /\
                                ((ei[self] <= K /\ ~wrapped(lo'[self],ei[self])) \/
                                 (ei[self] > K /\ wrapped(lo'[self],ei[self])))
                                THEN /\ newexternal' =         Append(newexternal \o
                                                       subSeqSmaller(external, newexternal, lo'[self]), lo'[self])
                                     /\ table' = [table EXCEPT ![mod(ei[self], K)] = lo'[self] * (-1)]
                                ELSE /\ TRUE
                                     /\ UNCHANGED << table, newexternal >>
                          /\ ei' = [ei EXCEPT ![self] = ei[self] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "flush"]
                          /\ UNCHANGED external
                     ELSE /\ external' = newexternal \o
                                          subSeqLarger(external, newexternal)
                          /\ newexternal' = <<>>
                          /\ pc' = [pc EXCEPT ![self] = "rtrn"]
                          /\ UNCHANGED << table, ei, lo >>
               /\ UNCHANGED << evict, waitCnt, history, stack, ej, fp, index, 
                               result, expected >>

rtrn(self) == /\ pc[self] = "rtrn"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ ei' = [ei EXCEPT ![self] = Head(stack[self]).ei]
              /\ ej' = [ej EXCEPT ![self] = Head(stack[self]).ej]
              /\ lo' = [lo EXCEPT ![self] = Head(stack[self]).lo]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                              history, fp, index, result, expected >>

Evict(self) == strIns(self) \/ nestedIns(self) \/ set(self) \/ flush(self)
                  \/ rtrn(self)

pick(self) == /\ pc[self] = "pick"
              /\ IF (fps \ history) = {}
                    THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ fp' = fp
                    ELSE /\ \E f \in (fps \ history):
                              fp' = [fp EXCEPT ![self] = f]
                         /\ pc' = [pc EXCEPT ![self] = "put"]
              /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                              history, stack, ei, ej, lo, index, result, 
                              expected >>

put(self) == /\ pc[self] = "put"
             /\ index' = [index EXCEPT ![self] = 0]
             /\ result' = [result EXCEPT ![self] = FALSE]
             /\ expected' = [expected EXCEPT ![self] = L]
             /\ IF evict
                   THEN /\ waitCnt' = waitCnt + 1
                        /\ pc' = [pc EXCEPT ![self] = "waitEv"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "chkSnc"]
                        /\ UNCHANGED waitCnt
             /\ UNCHANGED << table, external, newexternal, evict, history, 
                             stack, ei, ej, lo, fp >>

waitEv(self) == /\ pc[self] = "waitEv"
                /\ evict = FALSE
                /\ pc' = [pc EXCEPT ![self] = "endWEv"]
                /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                                history, stack, ei, ej, lo, fp, index, result, 
                                expected >>

endWEv(self) == /\ pc[self] = "endWEv"
                /\ waitCnt' = waitCnt - 1
                /\ pc' = [pc EXCEPT ![self] = "put"]
                /\ UNCHANGED << table, external, newexternal, evict, history, 
                                stack, ei, ej, lo, fp, index, result, expected >>

chkSnc(self) == /\ pc[self] = "chkSnc"
                /\ IF external # <<>>
                      THEN /\ pc' = [pc EXCEPT ![self] = "cntns"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "insrt"]
                /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                                history, stack, ei, ej, lo, fp, index, result, 
                                expected >>

cntns(self) == /\ pc[self] = "cntns"
               /\ IF index[self] < L
                     THEN /\ IF isMatch(fp[self], idx(fp[self], index[self]), table)
                                THEN /\ pc' = [pc EXCEPT ![self] = "pick"]
                                     /\ UNCHANGED << index, expected >>
                                ELSE /\ IF isEmpty(idx(fp[self], index[self]), table)
                                           THEN /\ expected' = [expected EXCEPT ![self] = minimum(expected[self], index[self])]
                                                /\ pc' = [pc EXCEPT ![self] = "onSnc"]
                                                /\ index' = index
                                           ELSE /\ IF isMarked(idx(fp[self], index[self]), table)
                                                      THEN /\ expected' = [expected EXCEPT ![self] = minimum(expected[self], index[self])]
                                                           /\ index' = [index EXCEPT ![self] = index[self] + 1]
                                                      ELSE /\ index' = [index EXCEPT ![self] = index[self] + 1]
                                                           /\ UNCHANGED expected
                                                /\ pc' = [pc EXCEPT ![self] = "cntns"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "onSnc"]
                          /\ UNCHANGED << index, expected >>
               /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                               history, stack, ei, ej, lo, fp, result >>

onSnc(self) == /\ pc[self] = "onSnc"
               /\ IF containsElem(external,fp[self])
                     THEN /\ pc' = [pc EXCEPT ![self] = "pick"]
                          /\ UNCHANGED << index, expected >>
                     ELSE /\ index' = [index EXCEPT ![self] = expected[self]]
                          /\ expected' = [expected EXCEPT ![self] = -1]
                          /\ pc' = [pc EXCEPT ![self] = "insrt"]
               /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                               history, stack, ei, ej, lo, fp, result >>

insrt(self) == /\ pc[self] = "insrt"
               /\ IF index[self] < L
                     THEN /\ expected' = [expected EXCEPT ![self] = table[idx(fp[self],index[self])]]
                          /\ IF expected'[self] = empty \/
                                (expected'[self] < 0 /\ expected'[self] # (-1) * fp[self])
                                THEN /\ pc' = [pc EXCEPT ![self] = "cas"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "isMth"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "tryEv"]
                          /\ UNCHANGED expected
               /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                               history, stack, ei, ej, lo, fp, index, result >>

isMth(self) == /\ pc[self] = "isMth"
               /\ IF isMatch(fp[self],idx(fp[self],index[self]),table)
                     THEN /\ pc' = [pc EXCEPT ![self] = "pick"]
                          /\ index' = index
                     ELSE /\ index' = [index EXCEPT ![self] = index[self] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "insrt"]
               /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                               history, stack, ei, ej, lo, fp, result, 
                               expected >>

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
             /\ UNCHANGED << external, newexternal, evict, waitCnt, stack, ei, 
                             ej, lo, fp, index, expected >>

tryEv(self) == /\ pc[self] = "tryEv"
               /\ IF evict = FALSE
                     THEN /\ evict' = TRUE
                          /\ pc' = [pc EXCEPT ![self] = "waitIns"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "put"]
                          /\ evict' = evict
               /\ UNCHANGED << table, external, newexternal, waitCnt, history, 
                               stack, ei, ej, lo, fp, index, result, expected >>

waitIns(self) == /\ pc[self] = "waitIns"
                 /\ waitCnt = Cardinality(Writer) - 1 + Cardinality(Reader)
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Evict",
                                                          pc        |->  "endEv",
                                                          ei        |->  ei[self],
                                                          ej        |->  ej[self],
                                                          lo        |->  lo[self] ] >>
                                                      \o stack[self]]
                 /\ ei' = [ei EXCEPT ![self] = 1]
                 /\ ej' = [ej EXCEPT ![self] = 1]
                 /\ lo' = [lo EXCEPT ![self] = 0]
                 /\ pc' = [pc EXCEPT ![self] = "strIns"]
                 /\ UNCHANGED << table, external, newexternal, evict, waitCnt, 
                                 history, fp, index, result, expected >>

endEv(self) == /\ pc[self] = "endEv"
               /\ evict' = FALSE
               /\ pc' = [pc EXCEPT ![self] = "put"]
               /\ UNCHANGED << table, external, newexternal, waitCnt, history, 
                               stack, ei, ej, lo, fp, index, result, expected >>

p(self) == pick(self) \/ put(self) \/ waitEv(self) \/ endWEv(self)
              \/ chkSnc(self) \/ cntns(self) \/ onSnc(self) \/ insrt(self)
              \/ isMth(self) \/ cas(self) \/ tryEv(self) \/ waitIns(self)
              \/ endEv(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Evict(self))
           \/ (\E self \in Writer: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Writer : WF_vars(p(self)) /\ WF_vars(Evict(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

----------------------------------------------------------------------------

contains(f,t,seq,Q) == \/ \E i \in 0..Q: isMatch(f,idx(f,i),t)
                       \/ \E i \in 1..Len(seq): seq[i] = f
                       \/ IF f \in (Image(lo) \ {0}) THEN evict = TRUE
                                                     ELSE FALSE

(***************************************************************************)
(* All fingerprint in history are (always) members of the seen set C,      *)
(* all (fps \ history) never are.                                          *)
(* During eviction, the sort algorithm might swap two fingerprints         *)
(* non-atomically s.t. the table does not contain one of the two           *)
(* fingerprints. The one not in table is then expected to be in the lo     *)
(* variable of the sort algorithms.                                        *)
(***************************************************************************)
Contains == /\ \A seen \in history: 
                           contains(seen,table,external,L)
            /\ \A unseen \in (fps \ history):
                          ~contains(unseen,table,external,L)

----------------------------------------------------------------------------

(***************************************************************************)
(* The absolute value of the given number.                                 *)
(***************************************************************************)
abs(number) == IF number < 0 THEN -1 * number ELSE number
       
(***************************************************************************)
(* True when no eviction is running.                                       *)
(***************************************************************************)
FindOrPut == evict = FALSE

(***************************************************************************)
(* FALSE iff table contains duplicate elements (excluding empty), unless   *)
(* Evict is running.                                                       *)
(* During eviction, the sort algorithm might swap two fingerprints         *)
(* non-atomically s.t. the table contains duplicates of one of the two     *)
(* fingerprints temporarily.                                               *)
(***************************************************************************)
Duplicates == FindOrPut => LET sub == SelectSeq(table, LAMBDA e: e # empty)
                           IN IF Len(sub) < 2 THEN TRUE
                              ELSE \A i \in 1..(Len(sub) - 1):
                                      \A j \in (i+1)..Len(sub):
                                         abs(sub[i]) # abs(sub[j])

----------------------------------------------------------------------------

(***************************************************************************)
(* seq is sorted iff its empty-filtered sub-sequence is sorted. An empty   *)
(* sequence is defined to be sorted.                                       *)
(***************************************************************************)
isSorted(seq) == LET sub == SelectSeq(seq, LAMBDA e: e # empty)
                 IN IF Len(sub) < 2 THEN TRUE
                    ELSE \A i \in 1..(Len(sub) - 1):
                            sub[i] < sub[i+1]
                        
(***************************************************************************)
(* External storage is always sorted in ascending order.                   *)
(***************************************************************************) 
Sorted == isSorted(external) /\ isSorted(newexternal)

----------------------------------------------------------------------------

(***************************************************************************)
(* TRUE iff f is found in table within idx(f,0)..id(f,L).                  *)
(***************************************************************************)
containedInTable(f) == \E l \in 0..L: table[idx(abs(f), l)] = f

(***************************************************************************)
(* TRUE if all fingerprints \in history correctly transition from table    *)
(* to the external storage. Models a three state FSM.                      *)
(***************************************************************************)
Consistent == FindOrPut => \A seen \in history:
            /\ containedInTable(seen) => ~containsElem(external, seen)
            /\ containedInTable(seen * (-1)) => containsElem(external, seen)
            /\ ~containedInTable(seen) => containsElem(external, seen)

----------------------------------------------------------------------------

(***************************************************************************)
(* Under all behaviors, the algorithm makes progress and eventually puts   *)
(* all fingerprints in fps into the table resulting in history = fps.      *)
(***************************************************************************)
Complete == <>[](history = fps)

(***************************************************************************)
(* Iff certain that Termination is guaranteed, the liveness property       *)
(* Complete can be rewritten to the safety property below. A safety        *)
(* property can be checked faster.                                         *)
(***************************************************************************)
CompleteAsSafety == \A self \in ProcSet: pc[self] = "Done" => (history = fps)
=============================================================================
\end{ppcal}