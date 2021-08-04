------------------------------- MODULE MergeSort ----------------------------- 
EXTENDS Naturals, Sequences, TLC

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat

ASSUME Print(<<"Testing Mergesort on all arrays of length <= ", ArrayLen>>,
             TRUE)

PermsOf(Arr) ==
  LET Automorphism(S) == { f \in [S -> S] : 
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphism(DOMAIN Arr) }

(*   

Copied from page 166 of the 2nd edition of Robert Sedgewick's "Algorithms".

--algorithm Mergesort
  variables a \in UNION {[1..N -> 1..N] : N \in 0..ArrayLen} ;
            b = [x \in DOMAIN a |-> 99]  \* ;
  procedure mergesort(l, r)
    variables i ; j  ; k ; m \* ; 
    begin l1: if r - l > 0
                then      m := (r + l) \div 2 ;
                     l2 : call mergesort(l, m) ;
                     l3 : call mergesort(m+1, r) ;
                     l4 : i := m ;
                     l5 : while i \geq l
                            do b[i] := a[i];
                               i := i - 1 \* ;
                          end while ;
                          (*************************************************)
                          (* I don't know what the Pascal statement        *)
                          (*                                               *)
                          (*       for i := m downto l ...                 *)
                          (*                                               *)
                          (* is supposed to set i to if m < l, so the      *)
                          (* algorithm reports an error and stops in this    *)
                          (*************************************************)
                          if m \geq l
                            then i := l ; 
                            else print "not sure of semantics of Pascal" ;
                                 i := CHOOSE x \in {} : FALSE ;
                          end if ;
                          j := m + 1 ;
                     l6 : while j \leq r
                            do b[r + m + 1 - j] := a[j] ;
                               j := j + 1 ;
                          end while ;
                          (*************************************************)
                          (* I don't know what the Pascal statement        *)
                          (*                                               *)
                          (*       for j := m+1 to r ...                   *)
                          (*                                               *)
                          (* is supposed to set j to if m+1 < r, so the    *)
                          (* algorithm reports an error and stops in this    *)
                          (*************************************************)
                          if m+1 \leq r
                            then j := r ;  
                            else print "not sure of semantics of Pascal" ;
                                 i := CHOOSE x \in {} : FALSE ;
                          end if ;
                          k := l ;
                     l7 : while k \leq r
                            do if b[i] < b[j]
                                 then a[k] := b[i] ;
                                      i := i + 1 ;
                                 else a[k] := b[j] ;
                                      j := j - 1 ;
                               end if ;
                            k := k + 1 ;
                          end while ;
              end if ;
          l8: return ;
    end procedure
  begin  main : call mergesort (1, Len(a)) ;
  end algorithm
*)
                    
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-3f24d15c1de7a8bf341d55378b5a76c0
CONSTANT defaultInitValue
VARIABLES a, b, pc, stack, l, r, i, j, k, m

vars == << a, b, pc, stack, l, r, i, j, k, m >>

Init == (* Global variables *)
        /\ a \in UNION {[1..N -> 1..N] : N \in 0..ArrayLen}
        /\ b = [x \in DOMAIN a |-> 99]
        (* Procedure mergesort *)
        /\ l = defaultInitValue
        /\ r = defaultInitValue
        /\ i = defaultInitValue
        /\ j = defaultInitValue
        /\ k = defaultInitValue
        /\ m = defaultInitValue
        /\ stack = << >>
        /\ pc = "main"

l1 == /\ pc = "l1"
      /\ IF r - l > 0
            THEN /\ m' = ((r + l) \div 2)
                 /\ pc' = "l2"
            ELSE /\ pc' = "l8"
                 /\ m' = m
      /\ UNCHANGED << a, b, stack, l, r, i, j, k >>

l2 == /\ pc = "l2"
      /\ /\ l' = l
         /\ r' = m
         /\ stack' = << [ procedure |->  "mergesort",
                          pc        |->  "l3",
                          i         |->  i,
                          j         |->  j,
                          k         |->  k,
                          m         |->  m,
                          l         |->  l,
                          r         |->  r ] >>
                      \o stack
      /\ i' = defaultInitValue
      /\ j' = defaultInitValue
      /\ k' = defaultInitValue
      /\ m' = defaultInitValue
      /\ pc' = "l1"
      /\ UNCHANGED << a, b >>

l3 == /\ pc = "l3"
      /\ /\ l' = m+1
         /\ r' = r
         /\ stack' = << [ procedure |->  "mergesort",
                          pc        |->  "l4",
                          i         |->  i,
                          j         |->  j,
                          k         |->  k,
                          m         |->  m,
                          l         |->  l,
                          r         |->  r ] >>
                      \o stack
      /\ i' = defaultInitValue
      /\ j' = defaultInitValue
      /\ k' = defaultInitValue
      /\ m' = defaultInitValue
      /\ pc' = "l1"
      /\ UNCHANGED << a, b >>

l4 == /\ pc = "l4"
      /\ i' = m
      /\ pc' = "l5"
      /\ UNCHANGED << a, b, stack, l, r, j, k, m >>

l5 == /\ pc = "l5"
      /\ IF i \geq l
            THEN /\ b' = [b EXCEPT ![i] = a[i]]
                 /\ i' = i - 1
                 /\ pc' = "l5"
                 /\ j' = j
            ELSE /\ IF m \geq l
                       THEN /\ i' = l
                       ELSE /\ PrintT("not sure of semantics of Pascal")
                            /\ i' = (CHOOSE x \in {} : FALSE)
                 /\ j' = m + 1
                 /\ pc' = "l6"
                 /\ b' = b
      /\ UNCHANGED << a, stack, l, r, k, m >>

l6 == /\ pc = "l6"
      /\ IF j \leq r
            THEN /\ b' = [b EXCEPT ![r + m + 1 - j] = a[j]]
                 /\ j' = j + 1
                 /\ pc' = "l6"
                 /\ UNCHANGED << i, k >>
            ELSE /\ IF m+1 \leq r
                       THEN /\ j' = r
                            /\ i' = i
                       ELSE /\ PrintT("not sure of semantics of Pascal")
                            /\ i' = (CHOOSE x \in {} : FALSE)
                            /\ j' = j
                 /\ k' = l
                 /\ pc' = "l7"
                 /\ b' = b
      /\ UNCHANGED << a, stack, l, r, m >>

l7 == /\ pc = "l7"
      /\ IF k \leq r
            THEN /\ IF b[i] < b[j]
                       THEN /\ a' = [a EXCEPT ![k] = b[i]]
                            /\ i' = i + 1
                            /\ j' = j
                       ELSE /\ a' = [a EXCEPT ![k] = b[j]]
                            /\ j' = j - 1
                            /\ i' = i
                 /\ k' = k + 1
                 /\ pc' = "l7"
            ELSE /\ pc' = "l8"
                 /\ UNCHANGED << a, i, j, k >>
      /\ UNCHANGED << b, stack, l, r, m >>

l8 == /\ pc = "l8"
      /\ pc' = Head(stack).pc
      /\ i' = Head(stack).i
      /\ j' = Head(stack).j
      /\ k' = Head(stack).k
      /\ m' = Head(stack).m
      /\ l' = Head(stack).l
      /\ r' = Head(stack).r
      /\ stack' = Tail(stack)
      /\ UNCHANGED << a, b >>

mergesort == l1 \/ l2 \/ l3 \/ l4 \/ l5 \/ l6 \/ l7 \/ l8

main == /\ pc = "main"
        /\ /\ l' = 1
           /\ r' = Len(a)
           /\ stack' = << [ procedure |->  "mergesort",
                            pc        |->  "Done",
                            i         |->  i,
                            j         |->  j,
                            k         |->  k,
                            m         |->  m,
                            l         |->  l,
                            r         |->  r ] >>
                        \o stack
        /\ i' = defaultInitValue
        /\ j' = defaultInitValue
        /\ k' = defaultInitValue
        /\ m' = defaultInitValue
        /\ pc' = "l1"
        /\ UNCHANGED << a, b >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == mergesort \/ main
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ff6c7e89b9c9baac60a504f5cbacb5a2

Invariant == 
   (pc = "Done") => \A x, y \in DOMAIN a :
                       (x < y) => a[x] \leq a[y]
=============================================================================
