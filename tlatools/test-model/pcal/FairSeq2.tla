------------------------------ MODULE FairSeq2 ------------------------------
EXTENDS Integers
(***************************************************************************
PlusCal options (version 1.5)
--fair algorithm FairSeq {
    variable x = 0 ;
    fair { while (x < 10) {
            x := x+1;
         }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION PC-755164df2e2bd65e9569f4d78be1801bb6d9ca6b02d3e1cfd34ce0fab635434d
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x < 10
               THEN /\ x' = x+1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION TPC-9037c011edf54e46da7478c88cda9045db618e0b27957dbea2c72c4b044f5c09
=============================================================================
\* Modification History
\* Last modified Sun Mar 20 10:13:11 PDT 2011 by lamport
\* Created Sun Mar 20 10:10:54 PDT 2011 by lamport
