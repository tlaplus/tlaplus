------------------------------- MODULE MultiUser -------------------------------

EXTENDS Base

SingleUser2 == INSTANCE SingleUser WITH
                UserIDs <- {2},
                State <- 2 :> State[2] 

SingleUser3 == INSTANCE SingleUser WITH
                UserIDs <- {3},
                State <- 2 :> State[2] 

SingleUserP(n) == INSTANCE SingleUser WITH
                UserIDs <- {n},
                State <- n :> State[n] 

Init ==
    StateMachine!Init(UserIDs)
    
Next ==
    \E user \in UserIDs : StateMachine!Next(user)

Spec ==
    /\ Init
    /\ [][Next]_State

=============================================================================