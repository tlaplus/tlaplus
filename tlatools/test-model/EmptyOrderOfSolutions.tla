----- MODULE EmptyOrderOfSolutions -----
VARIABLES x

Init == x = 0

Next == x' = 1

Spec == Init /\ [][Next]_x

Prop == <>[]TRUE => TRUE
=====
