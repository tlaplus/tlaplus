-------- MODULE CdotWithContextA ---------
EXTENDS Naturals

VARIABLE x, S

Init ==
    x = 0 /\ S = {1,2}

A(n) ==
    /\ x' = n
    /\ UNCHANGED S
    

B(n) ==
    /\ x' = n + 1
	/\ UNCHANGED S

Next ==
	/\ x = 0
    /\ \E n \in S :
          /\ n \in S
          /\ A(n) \cdot B(n)

Spec ==
    Init /\ [][Next]_<<S, x>>

=======