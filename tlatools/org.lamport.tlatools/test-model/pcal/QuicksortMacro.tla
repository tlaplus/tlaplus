---------------------------- MODULE QuicksortMacro --------------------------- 
EXTENDS Naturals, Sequences

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat

PermsOf(Arr) ==
  LET Automorphism(S) == { f \in [S -> S] : 
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphism(DOMAIN Arr) }

(*   
--algorithm QuicksortMacro
  variables A \in [1..ArrayLen -> 1..ArrayLen];
            returnVal = 1;
  macro Partition(lo, hi)
    begin      with piv \in lo..(hi-1)
                  do returnVal := piv ;
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
                  then       Partition(qlo, qhi) ;
                       qs2 : pivot := returnVal ;
                       qs3 : call QS(qlo, pivot) ;
                       qs4 : call QS(pivot +1,qhi) ;
                             return ;
                  else    return;
                end if;
    end procedure
  begin  main : call QS(1, Len(A)) ;
  end algorithm
*)
                    
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-f3c86b18c12d46dfb100d83f44bd15cc
VARIABLES A, returnVal, pc, stack, qlo, qhi, pivot

vars == << A, returnVal, pc, stack, qlo, qhi, pivot >>

Init == (* Global variables *)
        /\ A \in [1..ArrayLen -> 1..ArrayLen]
        /\ returnVal = 1
        (* Procedure QS *)
        /\ qlo = 1
        /\ qhi = 1
        /\ pivot = 1
        /\ stack = << >>
        /\ pc = "main"

qs1 == /\ pc = "qs1"
       /\ IF qlo < qhi
             THEN /\ \E piv \in qlo..(qhi-1):
                       /\ returnVal' = piv
                       /\ \E Ap \in {AA \in PermsOf(A) :
                                           (\A i \in 1..(qlo-1) : AA[i] = A[i])
                                        /\ (\A i \in (qhi+1)..Len(A) : AA[i] = A[i])
                                        /\ (\A i \in qlo..piv, j \in (piv+1)..qhi :
                                                AA[i] \leq AA[j])}:
                            A' = Ap
                  /\ pc' = "qs2"
                  /\ UNCHANGED << stack, qlo, qhi, pivot >>
             ELSE /\ pc' = Head(stack).pc
                  /\ pivot' = Head(stack).pivot
                  /\ qlo' = Head(stack).qlo
                  /\ qhi' = Head(stack).qhi
                  /\ stack' = Tail(stack)
                  /\ UNCHANGED << A, returnVal >>

qs2 == /\ pc = "qs2"
       /\ pivot' = returnVal
       /\ pc' = "qs3"
       /\ UNCHANGED << A, returnVal, stack, qlo, qhi >>

qs3 == /\ pc = "qs3"
       /\ /\ qhi' = pivot
          /\ qlo' = qlo
          /\ stack' = << [ procedure |->  "QS",
                           pc        |->  "qs4",
                           pivot     |->  pivot,
                           qlo       |->  qlo,
                           qhi       |->  qhi ] >>
                       \o stack
       /\ pivot' = 1
       /\ pc' = "qs1"
       /\ UNCHANGED << A, returnVal >>

qs4 == /\ pc = "qs4"
       /\ /\ qhi' = qhi
          /\ qlo' = pivot +1
       /\ pivot' = 1
       /\ pc' = "qs1"
       /\ UNCHANGED << A, returnVal, stack >>

QS == qs1 \/ qs2 \/ qs3 \/ qs4

main == /\ pc = "main"
        /\ /\ qhi' = Len(A)
           /\ qlo' = 1
           /\ stack' = << [ procedure |->  "QS",
                            pc        |->  "Done",
                            pivot     |->  pivot,
                            qlo       |->  qlo,
                            qhi       |->  qhi ] >>
                        \o stack
        /\ pivot' = 1
        /\ pc' = "qs1"
        /\ UNCHANGED << A, returnVal >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == QS \/ main
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-f36591cc8efd54110514a4b1f13d3500

Invariant == 
   (pc = "Done") => \A i, j \in 1..ArrayLen :
                       (i < j) => A[i] \leq A[j]


=============================================================================
