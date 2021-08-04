-------------------------- MODULE MacroRealQuicksort ------------------------- 
EXTENDS Naturals, Sequences, TLC

CONSTANT N

ASSUME N \in Nat

PermsOf(Arr) ==
  LET Automorphism(S) == { f \in [S -> S] : 
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphism(DOMAIN Arr) }

(*   
--algorithm Quicksort
  variables Ainit \in [1..N -> 1..N]; A = Ainit;
            S = {<<1,N>>} ; pivot = 1 ;
  macro Partition(pivot, lo, hi)
    begin   with piv \in lo..(hi-1)
              do pivot := piv ;
                 with Ap \in
                      {AA \in PermsOf(A) :
                             (\A i \in 1..(lo-1) : AA[i] = A[i])
                          /\ (\A i \in (hi+1)..Len(A) : AA[i] = A[i])
                          /\ (\A i \in lo..piv, j \in (piv+1)..hi :
                                  AA[i] \leq AA[j])}
                   do A := Ap;
                   end with ;
              end with;
    end macro
   begin qs1 : while S # {}
                do with I \in S
                   do if I[1] < I[2]
                        then Partition(pivot, I[1], I[2]) ;
                             S := (S \ {I}) 
                                    \cup {<<I[1], pivot>>, <<pivot+1, I[2]>>}
                        else S := (S \ {I}) 
                    end if
                   end with
                end while
  end algorithm
*)
                    
\* BEGIN TRANSLATION
VARIABLES Ainit, A, S, pivot, pc

vars == << Ainit, A, S, pivot, pc >>

Init == (* Global variables *)
        /\ Ainit \in [1..N -> 1..N]
        /\ A = Ainit
        /\ S = {<<1,N>>}
        /\ pivot = 1
        /\ pc = "qs1"

qs1 == /\ pc = "qs1"
       /\ IF S # {}
             THEN /\ \E I \in S:
                       IF I[1] < I[2]
                          THEN /\ \E piv \in (I[1])..((I[2])-1):
                                    /\ pivot' = piv
                                    /\ \E Ap \in {AA \in PermsOf(A) :
                                                        (\A i \in 1..((I[1])-1) : AA[i] = A[i])
                                                     /\ (\A i \in ((I[2])+1)..Len(A) : AA[i] = A[i])
                                                     /\ (\A i \in (I[1])..piv, j \in (piv+1)..(I[2]) :
                                                             AA[i] \leq AA[j])}:
                                         A' = Ap
                               /\ S' = (S \ {I})
                                         \cup {<<I[1], pivot'>>, <<pivot'+1, I[2]>>}
                          ELSE /\ S' = (S \ {I})
                               /\ UNCHANGED << A, pivot >>
                  /\ pc' = "qs1"
             ELSE /\ pc' = "Done"
                  /\ UNCHANGED << A, S, pivot >>
       /\ Ainit' = Ainit

Next == qs1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================
Checked without termination on svc-lamport-2 with 2 workers:
  arrayLen = 4 in 15 sec, 32280 states, depth 22
  arrayLen = 5 in 138min 17 sec 1529005 states, depth 28
