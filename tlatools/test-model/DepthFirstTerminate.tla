---------------------------- MODULE DepthFirstTerminate ----------------------------
EXTENDS Integers

(*

--algorithm Untitled
{
    variables u = 24 ; v \in 1 .. 50;
    {
        print <<u, v>>;
        while (u # 0) {
            if (u < v) {
                u := v || v := u
            };
            u := u - v ;
        };
        print <<"have gcd", v>>;
    }
}
*)
\* BEGIN TRANSLATION
VARIABLES u, v, pc

vars == << u, v, pc >>

Init == (* Global variables *)
        /\ u = 24
        /\ v \in 1 .. 50
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << u, v >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF u # 0
               THEN /\ IF u < v
                          THEN /\ /\ u' = v
                                  /\ v' = u
                          ELSE /\ TRUE
                               /\ UNCHANGED << u, v >>
                    /\ pc' = "Lbl_3"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << u, v >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ u' = u - v
         /\ pc' = "Lbl_2"
         /\ v' = v

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
