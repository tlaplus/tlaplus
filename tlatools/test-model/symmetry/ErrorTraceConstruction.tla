------------------------- MODULE ErrorTraceConstruction -------------------------
EXTENDS Integers, TLC

S == {0,1}
Other(n) == CHOOSE x \in S \ {n} : TRUE

VARIABLES x, y

Init == x = 0 /\ y = 0

N0 == /\ y = 0
	  /\ y' = y+1
	  /\ x' = x
N1 == /\ y = 1
	  /\ y' = y+1
	  /\ x' = x
N2 == /\ y = 2
	  /\ y' = y+1
	  /\ x' = x
N3 == /\ y = 3
	  /\ y' = y+1
	  /\ x' = x
N4 == /\ y = 4
	  /\ y' = y+1
	  /\ x' = Other(x) \* flip x to violate Prop1
N5 == /\ y = 5
	  /\ y' = y+1
	  /\ x' = Other(x) \* flip x back to reduce the number of overall states
N6 == /\ y = 6
	  /\ y' = y+1
	  /\ x' = x
N7 == /\ y = 7
	  /\ y' = 3 \* loop to N3
	  /\ x' = x

Next == \/ N0
		\/ N1
		\/ N2
		\/ N3
		\/ N4
		\/ N5
		\/ N6
		\/ N7
           
Spec == Init /\ [][Next]_<<x, y>> /\ WF_<<x,y>>(Next)

Prop == <>[][x'=x]_<<x, y>>

=============================================================================
