------------------------------ MODULE J ------------------------------

VARIABLES x, y

Init == /\ x \in {1,2,3,4,5}
        /\ y = [i \in {1,2,3,4,5} |-> 0]

Foo(rcds) ==
 CASE x = 1 -> [ rcds EXCEPT ![x] = 42 ]
   [] OTHER -> rcds

Next == /\ y' = Foo(y)
        /\ UNCHANGED x 

Spec == Init /\ [][Next]_<<x,y>>
============
