-------------------------- MODULE SubsetValue --------------------------
EXTENDS Sequences, FiniteSets, Integers

(* 
  ASSUME Len(u) = Len(v)
  
  There exists a prefix p of u with length 0..Len(u)-1 s.t.
      /\ \A i \in 1..p: u[i] <= v[i]
      /\ u[p+1] < v[p+1]
  In other words, if u < v then there exists a prefix of u of length 0..(Len(u)-1)
  s.t. for all elements in the prefix of u are lower than the corresponding elements
  in the prefix of v. 
*)
Sorted(u, v) == \E p \in 0..(Len(u) - 1) : /\ \A q \in 1..p : u[q] <= v[q]
                                           /\ (u[p+1] + 1) = v[p+1]
                                         
-----------------------------------------------------------------------------

CONSTANT N,
         K

ASSUME /\ \A nn \in N: nn \in Nat
       /\ \A kk \in K: kk \in (Nat \ {0})
       \* n >= k \* Via a state constraint, to not explicitly handle this case in the 
                 \* algorithm. It makes no sense to draw subsets of cardinality k
                 \* out of n elements if k > n.

(* See Kunth's Volume 4 Fascicle 3, Generating All Combinations and Partitions (2005), 
   vi+150pp. ISBN 0-201-85394-9, http://www-cs-faculty.stanford.edu/~knuth/taocp.html
   (also http://www.cs.utsa.edu/~wagner/knuth/).
   "Efficiently Enumerating the Subsets of a Set" 2000 by Loughry, van Hemmert, and Schoofs
   found at http://www.applied-math.org/subset.pdf describe the same idea from a different
   perspective (providing a recursive algorithm).
   
   The purpuse of this algorithm is to generate the k-Subsets 
   { t \in SUBSET S : Cardinality(t) = k } out of the input set 0..(n-1) in a predefined
   order. Even though sets have no notion of order, the technical representation of a set
   in TLC has an order. This is e.g. important to efficiently determine equality of two
   or more sets. If all sets adhere to a predefined order, equality can be determined
   in O(n) time by a single pass over both sets.
   Let u and v be two k-Subsets for a given k. The (total) order defined by this algorithm
   is such that there exists a prefix p of u with length 0..Len(u)-1 s.t.
   \A i \in 1..p: u[i] <= v[i] /\ u[p+1] < v[p+1]  (see Sorted operator above).
--algorithm EnumerateSubsets {
  variables n \in N; k \in K;
            (* Represent sets as sequences because we are interested in order. *)
            s = <<>>; r = <<>>;
            i = 0; j = 0;
            (* A strictly monotonically increasing sequence from 0 to k-1 used to
               maintain the state of the algorithm.
               Let k = 4 and n = 5. Initially, idx is [0,1,2,3] which corresponds to the 
               first k-Subset with the first, second, third, fourth element of the 
               original input set (which does not appear in this spec because it is
               irrelevant for the actual algorithm). Next idx will change to [0,1,2,4],
               followed by [0,1,2,5], [0,1,3,4], [0,1,3,5], ... *)
            idx = [ii \in 0..(k - 1) |-> ii ];
    {
     (* The while below first generates the current k-subset determined by the state
        of idx and then mutates the state of idx to be ready to generate the next
         k-subset in the subsequent iteration. *)
     start:
     while (TRUE) {
       j := k - 1; i := k - 1; s := <<>>;
       
       (* The l1 loop serves two purposes:
          1) Generate the next k-Subset (depending on the state of idx)
             by doing a full pass over idx from end to front.
          2) As a byproduct, determine the next index i of idx which 
             has to be incremented.
       *)
       l1:
       while (j >= 0) {
           \* 2) Determine next i.
           if (idx[j] + k - j = n) {
                 i := j - 1;
           };
           \* 1) Prepend idx[j] to seq s.
           s := <<idx[j]>> \o s; j := j - 1;
       };
       \* Add s to the set r of k-Subsets. 
       r := Append(r, s);
       
       l2: 
       if (idx[0] = n - k) {
           goto Done;
       } else {
           (* Increment the i-th idx (by one) and for all higher indices
              h of i set idx[h] to idx[i] + (h - i). *)
           idx[i] := idx[i] + 1; i := i + 1;
           
           l3: 
           while (i < k) {
                idx[i] := idx[i - 1] + 1; i := i + 1;
           };
       };
     };
  }
}
*)
\* BEGIN TRANSLATION
\* omitted
\* END TRANSLATION

-----------------------------------------------------------------------------
\* Invariant and helpers:

\* SeqOfSeqsToSetOfSets(<< <<1>>, <<1,2>>, <<2,3,3>> >>) evals to {{1}, {1, 2}, {2, 3}}
SeqOfSeqsToSetOfSets(seq) == LET (* The image of function f with Op applied to each element f[x]. *)
                                 ImageApply(f, Op(_)) == { Op(f[x]) : x \in DOMAIN f }
                                 Image(f) == ImageApply(f, LAMBDA x : x) \* Lambda is just identity
                             IN ImageApply(seq, Image)

(* The set S of all k-subsets ks (Cardinality(ks) = k) for the range 0 to n - 1. 
   In other words, this is the expected set of subsets to be generated by the
   EnumerateSubsets above. *)
Expected == {ss \in SUBSET (0..(n-1)) : Cardinality(ss) = k }

Inv == (pc = "Done") => \* When terminated...
            \* ... the correct subsets have been generated...
            /\ Expected = SeqOfSeqsToSetOfSets(r)
            \* ... in the predefined order.
            /\ \A ii \in 1..Len(r) - 1: Sorted(r[ii], r[ii+1])

=============================================================================

