------------------------------ MODULE ULEuclid ------------------------------- 
(***************************************************************************)
(* Euclid's algorithm.                                                     *)
(***************************************************************************)

EXTENDS Naturals, TLC

CONSTANT MaxNum

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
  begin (*a :*) while u # 0
              do     if u < v then u := v || v := u ; end if ;
         (* b: *)  u := u - v;
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
                      


\* BEGIN TRANSLATION - the hash of the PCal code: PCal-15a96a62d4bb94349f0b7e97b7877563
VARIABLES u_ini, v_ini, u, v, pc

vars == << u_ini, v_ini, u, v, pc >>

Init == (* Global variables *)
        /\ u_ini \in 1 .. MaxNum
        /\ v_ini \in 1 .. MaxNum
        /\ u = u_ini
        /\ v = v_ini
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF u # 0
               THEN /\ IF u < v
                          THEN /\ /\ u' = v
                                  /\ v' = u
                          ELSE /\ TRUE
                               /\ UNCHANGED << u, v >>
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(v = GCD(u_ini, v_ini), 
                              "Failure of assertion at line 28, column 13.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << u, v >>
         /\ UNCHANGED << u_ini, v_ini >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ u' = u - v
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << u_ini, v_ini, v >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-42ac9bbadc686601495c6cb5a86d3d55


Invariant == 
   (pc = "Done") => (v = GCD(u_ini, v_ini))

=============================================================================
