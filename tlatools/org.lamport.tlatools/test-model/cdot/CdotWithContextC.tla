-------- MODULE CdotWithContextC ---------
EXTENDS Naturals

VARIABLE x, S

Init ==
    x = 0 /\ S = {1,2}

A(n) ==
    x' = n

B(n) ==
    /\ x' = n + 1

Next ==
	/\ x = 0
    /\ \E n \in S :
          /\ n \in S
          /\ A(n) \cdot B(n)
          /\ UNCHANGED S

Spec ==
    Init /\ [][Next]_<<S, x>>

=======