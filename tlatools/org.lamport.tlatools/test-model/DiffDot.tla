------------------- MODULE DiffDot ----------------------
EXTENDS Integers

VARIABLE x, y

Init ==
    x = 0 /\ y = "a"

Inc ==
    x' = x + 1

Dec ==
    x' = x - 1

Mul ==
    x' = x * 2

Div ==
    x' = x \div 2

Rst ==
    x' = 0

Stutt ==
    x' = x

Dis ==
    /\ x < 0
    /\ x' = x * (-1)
    
Next ==
 /\ y' = IF x % 2 = 0 THEN "a" ELSE "b"
 /\ \/ Inc
    \/ Dec
    \/ Mul
    \/ Div
    \/ Rst
\*    \/ Stutt
\*    \/ Dis

------------------------------------------------------------

Constraint == 
	x \in 0..5

============================================================