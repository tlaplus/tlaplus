------ MODULE Github525 ------
EXTENDS Naturals

VARIABLE x

Init ==
    /\  x = 1
    
Next ==
    /\  x < 5
    /\  x' = x + 1

Spec ==
    /\  Init
    /\ [][Next]_x
    \* Weak fairness starts with a box
    /\ []<>(ENABLED <<Next>>_x => []<><<Next>>_x)
    /\ WF_x(Next) 
    /\  ~<>~(x < 3) \* This one is not caught.
    \*/\ []FALSE
    /\ [](x < 3)
    
Invariant ==
    x < 4

Prop == [][x' \in {1, 2}]_x

THEOREM Spec => []Invariant

====
