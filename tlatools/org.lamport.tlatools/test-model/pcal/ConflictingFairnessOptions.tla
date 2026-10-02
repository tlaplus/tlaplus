---- MODULE ConflictingFairnessOptions ----

(*
PlusCal options (-nof)

--fair algorithm test
variables x = FALSE;
begin
    x := TRUE;
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "4ecfe369" /\ chksum(tla) = "4b91e06")
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x = FALSE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ x' = TRUE
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 

===========================================
