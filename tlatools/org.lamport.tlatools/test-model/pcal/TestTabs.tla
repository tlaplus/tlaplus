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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-df86b294351f95a8207d12196b3732f0
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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ec3da753015679c262e945265fc700f9
=============================================================================
