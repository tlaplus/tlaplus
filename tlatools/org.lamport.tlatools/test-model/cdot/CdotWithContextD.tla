-------- MODULE CdotWithContextD ---------
EXTENDS Naturals

VARIABLE x, S

Init ==
    x = 0 /\ S = {1,2}

A(n) ==
    x' = n

B(n) ==
    x' = n + 1

Next ==
	/\ x = 0
	/\ UNCHANGED S
    /\ \E n \in S :
          /\ n \in S
          /\ ( A(n) /\ S' = {} ) \cdot B(n) \* Next false

Spec ==
    Init /\ [][Next]_<<S,x>>

Prop ==
	[][Next]_<<S,x>>

Prop2 ==
	~(ENABLED Next)

=======