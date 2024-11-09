------------------------------ MODULE Example1 ------------------------------
EXTENDS Integers, TLC

VARIABLE x

Init == x = 0

Next == x' = ( x + 1 ) % 10

Spec == Init /\ [][Next]_<<x>> /\ []<><<TRUE>>_<<x>> 

Liveness1 == <>(x = -10)

Alias == [ x |-> x, l |-> TLCGet("level") ]

=============================================================================