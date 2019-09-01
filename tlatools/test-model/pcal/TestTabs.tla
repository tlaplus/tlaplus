------------------------------ MODULE TestTabs ------------------------------ 
\* Warning: there are evil tabs in this file.
EXTENDS Naturals, TLC
(*
--algorithm TestTabs
  variables x = 0 ;
  begin
l:  x := IF /\ \A i \in {1} : 1 + 1 = 2
	    /\ \A i \in {1} : 2 + 2 = 4
  	    /\	\/ \A i \in {1} : 
		   1 = 0
		\/ \A i \in {1} : 1 = 2
 	        \/ \A i \in {1} : 1 = 1
          THEN 1
          ELSE 0 ;
    assert x = 1 ;
  end algorithm
*)
\* BEGIN TRANSLATION PC-9e177812ae30787b295660b9055c8903874d634a7df9779a26828ff64cbfca5b
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x = 0
        /\ pc = "l"

l == /\ pc = "l"
     /\ x' = (IF /\ \A i \in {1} : 1 + 1 = 2
                 /\ \A i \in {1} : 2 + 2 = 4
                 /\  \/ \A i \in {1} :
                        1 = 0
                     \/ \A i \in {1} : 1 = 2
                     \/ \A i \in {1} : 1 = 1
               THEN 1
               ELSE 0)
     /\ Assert(x' = 1, "Failure of assertion at line 16, column 5.")
     /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION TPC-218ccbb896dc9260e1db905e46f8a9e6a9e50069d62fc43787ecf0dffe70e386
=============================================================================
