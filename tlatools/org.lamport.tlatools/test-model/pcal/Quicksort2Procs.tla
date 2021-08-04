--------------------------- MODULE Quicksort2Procs --------------------------- 
EXTENDS Naturals, Sequences

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat

PermsOf(Arr) ==
  LET Automorphism(S) == { f \in [S -> S] : 
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphism(DOMAIN Arr) }

(*   This algorithm uses two different copies of the QS procedure
     to test whether tail recursion works when calling a different
     procedure.

--algorithm Quicksort
  variables A \in [1..ArrayLen -> 1..ArrayLen];
            returnVal = 99;
  procedure Partition(lo = 99, hi = 99)
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
  procedure  QS(qlo = 99, qhi = 99)
    variable pivot = 99 ;
    begin qs1 : if qlo < qhi
                  then       call Partition(qlo, qhi) ;
                       qs2 : pivot := returnVal ;
                       qs3 : call QS2(qlo, pivot) ;
                       qs4 : call QS2(pivot +1,qhi) ;
                             return ;
                  else    return;
                end if;
    end procedure
  procedure  QS2(qlo2 = 99, qhi2 = 99)
    variable pivot2 = 99 ;
    begin 2qs1 : if qlo2 < qhi2
                  then       call Partition(qlo2, qhi2) ;
                       2qs2 : pivot2 := returnVal ;
                       2qs3 : call QS(qlo2, pivot2) ;
                       2qs4 : call QS(pivot2 +1,qhi2) ;
                             return ;
                  else    return;
                end if;
    end procedure
  begin  main : call QS(1, Len(A)) ;
  end algorithm
*)
                    
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-041626606cd9c50bd2700d7f84bf1f9c
VARIABLES A, returnVal, pc, stack, lo, hi, qlo, qhi, pivot, qlo2, qhi2, 
          pivot2

vars == << A, returnVal, pc, stack, lo, hi, qlo, qhi, pivot, qlo2, qhi2, 
           pivot2 >>

Init == (* Global variables *)
        /\ A \in [1..ArrayLen -> 1..ArrayLen]
        /\ returnVal = 99
        (* Procedure Partition *)
        /\ lo = 99
        /\ hi = 99
        (* Procedure QS *)
        /\ qlo = 99
        /\ qhi = 99
        /\ pivot = 99
        (* Procedure QS2 *)
        /\ qlo2 = 99
        /\ qhi2 = 99
        /\ pivot2 = 99
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
       /\ UNCHANGED << qlo, qhi, pivot, qlo2, qhi2, pivot2 >>

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
       /\ UNCHANGED << A, returnVal, qlo2, qhi2, pivot2 >>

qs2 == /\ pc = "qs2"
       /\ pivot' = returnVal
       /\ pc' = "qs3"
       /\ UNCHANGED << A, returnVal, stack, lo, hi, qlo, qhi, qlo2, qhi2, 
                       pivot2 >>

qs3 == /\ pc = "qs3"
       /\ /\ qhi2' = pivot
          /\ qlo2' = qlo
          /\ stack' = << [ procedure |->  "QS2",
                           pc        |->  "qs4",
                           pivot2    |->  pivot2,
                           qlo2      |->  qlo2,
                           qhi2      |->  qhi2 ] >>
                       \o stack
       /\ pivot2' = 99
       /\ pc' = "2qs1"
       /\ UNCHANGED << A, returnVal, lo, hi, qlo, qhi, pivot >>

qs4 == /\ pc = "qs4"
       /\ /\ pivot' = Head(stack).pivot
          /\ qhi2' = qhi
          /\ qlo2' = pivot +1
          /\ stack' = << [ procedure |->  "QS2",
                           pc        |->  Head(stack).pc,
                           pivot2    |->  pivot2,
                           qlo2      |->  qlo2,
                           qhi2      |->  qhi2 ] >>
                       \o Tail(stack)
       /\ pivot2' = 99
       /\ pc' = "2qs1"
       /\ UNCHANGED << A, returnVal, lo, hi, qlo, qhi >>

QS == qs1 \/ qs2 \/ qs3 \/ qs4

2qs1 == /\ pc = "2qs1"
        /\ IF qlo2 < qhi2
              THEN /\ /\ hi' = qhi2
                      /\ lo' = qlo2
                      /\ stack' = << [ procedure |->  "Partition",
                                       pc        |->  "2qs2",
                                       lo        |->  lo,
                                       hi        |->  hi ] >>
                                   \o stack
                   /\ pc' = "pt1"
                   /\ UNCHANGED << qlo2, qhi2, pivot2 >>
              ELSE /\ pc' = Head(stack).pc
                   /\ pivot2' = Head(stack).pivot2
                   /\ qlo2' = Head(stack).qlo2
                   /\ qhi2' = Head(stack).qhi2
                   /\ stack' = Tail(stack)
                   /\ UNCHANGED << lo, hi >>
        /\ UNCHANGED << A, returnVal, qlo, qhi, pivot >>

2qs2 == /\ pc = "2qs2"
        /\ pivot2' = returnVal
        /\ pc' = "2qs3"
        /\ UNCHANGED << A, returnVal, stack, lo, hi, qlo, qhi, pivot, qlo2, 
                        qhi2 >>

2qs3 == /\ pc = "2qs3"
        /\ /\ qhi' = pivot2
           /\ qlo' = qlo2
           /\ stack' = << [ procedure |->  "QS",
                            pc        |->  "2qs4",
                            pivot     |->  pivot,
                            qlo       |->  qlo,
                            qhi       |->  qhi ] >>
                        \o stack
        /\ pivot' = 99
        /\ pc' = "qs1"
        /\ UNCHANGED << A, returnVal, lo, hi, qlo2, qhi2, pivot2 >>

2qs4 == /\ pc = "2qs4"
        /\ /\ pivot2' = Head(stack).pivot2
           /\ qhi' = qhi2
           /\ qlo' = pivot2 +1
           /\ stack' = << [ procedure |->  "QS",
                            pc        |->  Head(stack).pc,
                            pivot     |->  pivot,
                            qlo       |->  qlo,
                            qhi       |->  qhi ] >>
                        \o Tail(stack)
        /\ pivot' = 99
        /\ pc' = "qs1"
        /\ UNCHANGED << A, returnVal, lo, hi, qlo2, qhi2 >>

QS2 == 2qs1 \/ 2qs2 \/ 2qs3 \/ 2qs4

main == /\ pc = "main"
        /\ /\ qhi' = Len(A)
           /\ qlo' = 1
           /\ stack' = << [ procedure |->  "QS",
                            pc        |->  "Done",
                            pivot     |->  pivot,
                            qlo       |->  qlo,
                            qhi       |->  qhi ] >>
                        \o stack
        /\ pivot' = 99
        /\ pc' = "qs1"
        /\ UNCHANGED << A, returnVal, lo, hi, qlo2, qhi2, pivot2 >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Partition \/ QS \/ QS2 \/ main
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-da193a603aa89ac5bf05f91d5ffaf922

Invariant == 
   (pc = "Done") => \A i, j \in 1..ArrayLen :
                       (i < j) => A[i] \leq A[j]

\* Tested on 28 June 2005 with arrayLen = 5 in
\*  2 hours 9 min 6.5 seconds on SVC-Lamport-3

=============================================================================
