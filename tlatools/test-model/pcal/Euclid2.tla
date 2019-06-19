--algorithm EuclidAlg
variables u = 24 ; v \in 1 .. N ; v_ini = v ;
begin
lp: while u # 0 do   
        if u < v then u := v || v := u ;   
        end if ; 
     a: u := u - v; 
    end while ; 
    assert v = GCD(24, v_ini) ;
end algorithm

-------------------------------- MODULE Euclid2 ------------------------------ 
EXTENDS Naturals, TLC
\*CONSTANT N
N == 500

GCD(x, y) == CHOOSE i \in (1..x) \cap (1..y) :
                /\ x % i = 0 
                /\ y % i = 0
                /\ \A j \in (1..x) \cap (1..y) :
                        /\ x % j = 0 
                        /\ y % j = 0
                        => i \geq j

(***** BEGIN TRANSLATION ***)
VARIABLES u, v, v_ini, pc

vars == << u, v, v_ini, pc >>

Init == (* Global variables *)
        /\ u = 24
        /\ v \in 1 .. N
        /\ v_ini = v
        /\ pc = "lp"

lp == /\ pc = "lp"
      /\ IF u # 0
            THEN /\ IF u < v
                       THEN /\ /\ u' = v
                               /\ v' = u
                       ELSE /\ TRUE
                            /\ UNCHANGED << u, v >>
                 /\ pc' = "a"
            ELSE /\ Assert(v = GCD(24, v_ini), 
                           "Failure of assertion at line 9, column 5.")
                 /\ pc' = "Done"
                 /\ UNCHANGED << u, v >>
      /\ v_ini' = v_ini

a == /\ pc = "a"
     /\ u' = u - v
     /\ pc' = "lp"
     /\ UNCHANGED << v, v_ini >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == lp \/ a
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

(***** END TRANSLATION ***)
 
=============================================================================
