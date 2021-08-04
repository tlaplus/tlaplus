---------------------------- MODULE MacroQuicksort --------------------------- 
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
  procedure  QS(qlo = 1, qhi = 1)
    variable pivot = 1 ;
    begin qs1 : if qlo < qhi
                  then       Partition(pivot, qlo, qhi) ;
                       qs2 : call QS(qlo, pivot) ;
                       qs3 : call QS(pivot +1,qhi) ;
                end if;
          qs4 : return ;
    end procedure
  begin  main : call QS(1, Len(A)) ;
         test : assert     A \in PermsOf(Ainit)
                       /\ \A i, j \in 1..ArrayLen : 
                            (i < j) =>  A[i] \leq A[j]
  end algorithm
*)
                    
\* BEGIN TRANSLATION
VARIABLES Ainit, A, pc, stack, qlo, qhi, pivot

vars == << Ainit, A, pc, stack, qlo, qhi, pivot >>

Init == (* Global variables *)
        /\ Ainit \in [1..ArrayLen -> 1..ArrayLen]
        /\ A = Ainit
        (* Procedure QS *)
        /\ qlo = 1
        /\ qhi = 1
        /\ pivot = 1
        /\ stack = << >>
        /\ pc = "main"

qs1 == /\ pc = "qs1"
       /\ IF qlo < qhi
             THEN /\ \E piv \in qlo..(qhi-1):
                       /\ pivot' = piv
                       /\ \E Ap \in {AA \in PermsOf(A) :
                                           (\A i \in 1..(qlo-1) : AA[i] = A[i])
                                        /\ (\A i \in (qhi+1)..Len(A) : AA[i] = A[i])
                                        /\ (\A i \in qlo..piv, j \in (piv+1)..qhi :
                                                AA[i] \leq AA[j])}:
                            A' = Ap
                  /\ pc' = "qs2"
             ELSE /\ pc' = "qs4"
                  /\ UNCHANGED << A, pivot >>
       /\ UNCHANGED << Ainit, stack, qlo, qhi >>

qs2 == /\ pc = "qs2"
       /\ /\ qhi' = pivot
          /\ qlo' = qlo
          /\ stack' = << [ procedure |->  "QS",
                           pc        |->  "qs3",
                           pivot     |->  pivot,
                           qlo       |->  qlo,
                           qhi       |->  qhi ] >>
                       \o stack
       /\ pivot' = 1
       /\ pc' = "qs1"
       /\ UNCHANGED << Ainit, A >>

qs3 == /\ pc = "qs3"
       /\ /\ qhi' = qhi
          /\ qlo' = pivot +1
          /\ stack' = << [ procedure |->  "QS",
                           pc        |->  "qs4",
                           pivot     |->  pivot,
                           qlo       |->  qlo,
                           qhi       |->  qhi ] >>
                       \o stack
       /\ pivot' = 1
       /\ pc' = "qs1"
       /\ UNCHANGED << Ainit, A >>

qs4 == /\ pc = "qs4"
       /\ pc' = Head(stack).pc
       /\ pivot' = Head(stack).pivot
       /\ qlo' = Head(stack).qlo
       /\ qhi' = Head(stack).qhi
       /\ stack' = Tail(stack)
       /\ UNCHANGED << Ainit, A >>

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
        /\ pivot' = 1
        /\ pc' = "qs1"
        /\ UNCHANGED << Ainit, A >>

test == /\ pc = "test"
        /\ Assert(    A \in PermsOf(Ainit)
                  /\ \A i, j \in 1..ArrayLen :
                       (i < j) =>  A[i] \leq A[j], 
                  "Failure of assertion at line 40, column 17.")
        /\ pc' = "Done"
        /\ UNCHANGED << Ainit, A, stack, qlo, qhi, pivot >>

Next == QS \/ main \/ test
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
