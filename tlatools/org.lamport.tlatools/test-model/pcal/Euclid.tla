-------------------------------- MODULE Euclid ------------------------------- 
(***************************************************************************)
(* Euclid's algorithm.                                                     *)
(***************************************************************************)

EXTENDS Naturals, TLC

\*CONSTANT MaxNum
MaxNum == 20

ASSUME MaxNum > 0

ASSUME /\ Print(<<"Testing Euclid's algorithm on all numbers between 1 and ",
                   MaxNum>>, TRUE)
       /\ Print("Most time spent evaluating naive definition of GCD for test",
                TRUE)

(******
Adapted from page 8 of the 2nd edition of Robert Sedgewick's "Algorithms".

--algorithm Euclid
  variables u_ini \in 1 .. MaxNum ; 
            v_ini \in 1 .. MaxNum ;
            u = u_ini ; v = v_ini ;
  begin a : while u # 0
              do     if u < v then u := v || v := u ; end if ;
                 b:  u := u - v;
            end while ;
            assert v = GCD(u_ini, v_ini) ;
            \* print <<"gcd of ", u_ini, v_ini, " equals ", v >> ;
  end algorithm 

*)
                    
GCD(x, y) == CHOOSE i \in (1..x) \cap (1..y) :
                /\ x % i = 0 
                /\ y % i = 0
                /\ \A j \in (1..x) \cap (1..y) :
                        /\ x % j = 0 
                        /\ y % j = 0
                        => i \geq j
                      


\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a069024aba51f10ce87a41824584b8ee
VARIABLES u_ini, v_ini, u, v, pc

vars == << u_ini, v_ini, u, v, pc >>

Init == (* Global variables *)
        /\ u_ini \in 1 .. MaxNum
        /\ v_ini \in 1 .. MaxNum
        /\ u = u_ini
        /\ v = v_ini
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF u # 0
           THEN /\ IF u < v
                      THEN /\ /\ u' = v
                              /\ v' = u
                      ELSE /\ TRUE
                           /\ UNCHANGED << u, v >>
                /\ pc' = "b"
           ELSE /\ Assert(v = GCD(u_ini, v_ini), 
                          "Failure of assertion at line 29, column 13.")
                /\ pc' = "Done"
                /\ UNCHANGED << u, v >>
     /\ UNCHANGED << u_ini, v_ini >>

b == /\ pc = "b"
     /\ u' = u - v
     /\ pc' = "a"
     /\ UNCHANGED << u_ini, v_ini, v >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-969126b68f5e9c79e9cbf33f45804301


Invariant == 
   (pc = "Done") => (v = GCD(u_ini, v_ini))

=============================================================================
