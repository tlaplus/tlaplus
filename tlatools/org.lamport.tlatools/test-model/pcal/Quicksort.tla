------------------------------- MODULE Quicksort ----------------------------- 
EXTENDS Naturals, Sequences, TLC

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat

PermsOf(Arr) ==
  LET Automorphism(S) == { f \in [S -> S] : 
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphism(DOMAIN Arr) }

(*   
--algorithm Quicksort
  variables Ainit \in [1..ArrayLen -> 1..ArrayLen]; A = Ainit;
            returnVal = 1
  procedure Partition(lo, hi )
    begin pt1 : with piv \in lo..(hi-1)
                  do returnVal := piv ;
                     with Ap \in
                      {AA \in PermsOf(A) :
                             (\A i \in 1..(lo-1) : AA[i] = A[i])
                          /\ (\A i \in (hi+1)..Len(A) : AA[i] = A[i])
                          /\ (\A i \in lo..piv, j \in (piv+1)..hi :
                                  AA[i] \leq AA[j])}
                        do A := Ap;
                        return ;
                     end with ;
                end with;
    end procedure
  procedure  QS(qlo, qhi )
    variable pivot ;
    begin qs1 : if qlo < qhi
                  then       call Partition(qlo, qhi) ;
                       qs2 : pivot := returnVal ;
                       qs3 : call QS(qlo, pivot) ;
                       qs4 : call QS(pivot +1,qhi) ;
                             return ;
                  else    return;
                end if;
    end procedure
  begin  main : call QS(1, Len(A)) ;
         test : assert     A \in PermsOf(Ainit)
                       /\ \A i, j \in 1..ArrayLen : 
                            (i < j) =>  A[i] \leq A[j]
  end algorithm
*)
                    
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9360dabbf03d04fb938a53e6f43a0dc3
CONSTANT defaultInitValue
VARIABLES Ainit, A, returnVal, pc, stack, lo, hi, qlo, qhi, pivot

vars == << Ainit, A, returnVal, pc, stack, lo, hi, qlo, qhi, pivot >>

Init == (* Global variables *)
        /\ Ainit \in [1..ArrayLen -> 1..ArrayLen]
        /\ A = Ainit
        /\ returnVal = 1
        (* Procedure Partition *)
        /\ lo = defaultInitValue
        /\ hi = defaultInitValue
        (* Procedure QS *)
        /\ qlo = defaultInitValue
        /\ qhi = defaultInitValue
        /\ pivot = defaultInitValue
        /\ stack = << >>
        /\ pc = "main"

pt1 == /\ pc = "pt1"
       /\ \E piv \in lo..(hi-1):
            /\ returnVal' = piv
            /\ \E Ap \in {AA \in PermsOf(A) :
                                (\A i \in 1..(lo-1) : AA[i] = A[i])
                             /\ (\A i \in (hi+1)..Len(A) : AA[i] = A[i])
                             /\ (\A i \in lo..piv, j \in (piv+1)..hi :
                                     AA[i] \leq AA[j])}:
                 /\ A' = Ap
                 /\ pc' = Head(stack).pc
                 /\ lo' = Head(stack).lo
                 /\ hi' = Head(stack).hi
                 /\ stack' = Tail(stack)
       /\ UNCHANGED << Ainit, qlo, qhi, pivot >>

Partition == pt1

qs1 == /\ pc = "qs1"
       /\ IF qlo < qhi
             THEN /\ /\ hi' = qhi
                     /\ lo' = qlo
                     /\ stack' = << [ procedure |->  "Partition",
                                      pc        |->  "qs2",
                                      lo        |->  lo,
                                      hi        |->  hi ] >>
                                  \o stack
                  /\ pc' = "pt1"
                  /\ UNCHANGED << qlo, qhi, pivot >>
             ELSE /\ pc' = Head(stack).pc
                  /\ pivot' = Head(stack).pivot
                  /\ qlo' = Head(stack).qlo
                  /\ qhi' = Head(stack).qhi
                  /\ stack' = Tail(stack)
                  /\ UNCHANGED << lo, hi >>
       /\ UNCHANGED << Ainit, A, returnVal >>

qs2 == /\ pc = "qs2"
       /\ pivot' = returnVal
       /\ pc' = "qs3"
       /\ UNCHANGED << Ainit, A, returnVal, stack, lo, hi, qlo, qhi >>

qs3 == /\ pc = "qs3"
       /\ /\ qhi' = pivot
          /\ qlo' = qlo
          /\ stack' = << [ procedure |->  "QS",
                           pc        |->  "qs4",
                           pivot     |->  pivot,
                           qlo       |->  qlo,
                           qhi       |->  qhi ] >>
                       \o stack
       /\ pivot' = defaultInitValue
       /\ pc' = "qs1"
       /\ UNCHANGED << Ainit, A, returnVal, lo, hi >>

qs4 == /\ pc = "qs4"
       /\ /\ qhi' = qhi
          /\ qlo' = pivot +1
       /\ pivot' = defaultInitValue
       /\ pc' = "qs1"
       /\ UNCHANGED << Ainit, A, returnVal, stack, lo, hi >>

QS == qs1 \/ qs2 \/ qs3 \/ qs4

main == /\ pc = "main"
        /\ /\ qhi' = Len(A)
           /\ qlo' = 1
           /\ stack' = << [ procedure |->  "QS",
                            pc        |->  "test",
                            pivot     |->  pivot,
                            qlo       |->  qlo,
                            qhi       |->  qhi ] >>
                        \o stack
        /\ pivot' = defaultInitValue
        /\ pc' = "qs1"
        /\ UNCHANGED << Ainit, A, returnVal, lo, hi >>

test == /\ pc = "test"
        /\ Assert(    A \in PermsOf(Ainit)
                  /\ \A i, j \in 1..ArrayLen :
                       (i < j) =>  A[i] \leq A[j], 
                  "Failure of assertion at line 44, column 17.")
        /\ pc' = "Done"
        /\ UNCHANGED << Ainit, A, returnVal, stack, lo, hi, qlo, qhi, pivot >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Partition \/ QS \/ main \/ test
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c890d98935ff53e5f234680508ac16aa
=============================================================================
Checked without termination on svc-lamport-2 with 2 workers:
  arrayLen = 4 in 15 sec, 32280 states, depth 22
  arrayLen = 5 in 138min 17 sec 1529005 states, depth 28
