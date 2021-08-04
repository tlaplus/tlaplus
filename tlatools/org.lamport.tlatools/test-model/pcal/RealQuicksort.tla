----------------------------- MODULE RealQuicksort --------------------------- 
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT MaxLen

ASSUME MaxLen \in Nat

PermsOf(Arr) ==
  LET Automorphism(S) == { f \in [S -> S] : 
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphism(DOMAIN Arr) }

Min(S) == CHOOSE i \in S : \A j \in S : i \leq j
Max(S) == CHOOSE i \in S : \A j \in S : i \geq j

(*   

--algorithm RealQuicksort
  variables A \in UNION {[1..N -> 1..N] : N \in 0..MaxLen};
            Uns = {1..Len(A)} ;
            new = {} ;
  procedure Part(parg)
    begin pt1 : with new1 \in
                      {Min(parg)..piv : piv \in parg \ {Max(parg)}}  do
                with new2 = parg \ new1      do
                new := {new1, new2} ;
                with Ap \in
                      {AA \in PermsOf(A) :
                             (\A i \in 1..Len(A) \ parg : AA[i] = A[i])
                          /\ (\A i \in new1, j \in new2 :
                                  AA[i] \leq AA[j])}  do
                A := Ap;
                return ;
                end with ;
                end with ;
                end with;
    end procedure
  begin rqs : while Uns # {}
               do with next \in Uns
                   do Uns := Uns \ {next};
                      if Cardinality(next) > 1
                        then call Part(next) ;
                        else new := {} ;
                      end if ;
                  end with ;
                  rqs2 : Uns := Uns \cup new ;
              end while;
  end algorithm

*)
                    
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-1f05a46c32a9d2bb1934b39aad724eed
CONSTANT defaultInitValue
VARIABLES A, Uns, new, pc, stack, parg

vars == << A, Uns, new, pc, stack, parg >>

Init == (* Global variables *)
        /\ A \in UNION {[1..N -> 1..N] : N \in 0..MaxLen}
        /\ Uns = {1..Len(A)}
        /\ new = {}
        (* Procedure Part *)
        /\ parg = defaultInitValue
        /\ stack = << >>
        /\ pc = "rqs"

pt1 == /\ pc = "pt1"
       /\ \E new1 \in {Min(parg)..piv : piv \in parg \ {Max(parg)}}:
            LET new2 == parg \ new1 IN
              /\ new' = {new1, new2}
              /\ \E Ap \in {AA \in PermsOf(A) :
                                  (\A i \in 1..Len(A) \ parg : AA[i] = A[i])
                               /\ (\A i \in new1, j \in new2 :
                                       AA[i] \leq AA[j])}:
                   /\ A' = Ap
                   /\ pc' = Head(stack).pc
                   /\ parg' = Head(stack).parg
                   /\ stack' = Tail(stack)
       /\ Uns' = Uns

Part == pt1

rqs == /\ pc = "rqs"
       /\ IF Uns # {}
             THEN /\ \E next \in Uns:
                       /\ Uns' = Uns \ {next}
                       /\ IF Cardinality(next) > 1
                             THEN /\ /\ parg' = next
                                     /\ stack' = << [ procedure |->  "Part",
                                                      pc        |->  "rqs2",
                                                      parg      |->  parg ] >>
                                                  \o stack
                                  /\ pc' = "pt1"
                                  /\ new' = new
                             ELSE /\ new' = {}
                                  /\ pc' = "rqs2"
                                  /\ UNCHANGED << stack, parg >>
             ELSE /\ pc' = "Done"
                  /\ UNCHANGED << Uns, new, stack, parg >>
       /\ A' = A

rqs2 == /\ pc = "rqs2"
        /\ Uns' = (Uns \cup new)
        /\ pc' = "rqs"
        /\ UNCHANGED << A, new, stack, parg >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Part \/ rqs \/ rqs2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-4de5033005d037379ed702fb72c5f705

Invariant == 
   (pc = "Done") => \A i, j \in 1..Len(A) :
                       (i < j) => A[i] \leq A[j]
=============================================================================
