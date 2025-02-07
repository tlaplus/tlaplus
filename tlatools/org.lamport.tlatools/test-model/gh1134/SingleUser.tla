------------------------------- MODULE SingleUser -------------------------------

EXTENDS Base

\* This assume is not evaluated!!!
ASSUME Cardinality(UserIDs) = 1

Init ==
\*  Verification succeeds with the following LET ... IN
\*  Verification fails without the following LET ... IN
\*    /\ LET a == 1
\*       IN
        StateMachine!Init(UserIDs)
    
Next ==
    \E user \in UserIDs : StateMachine!Next(user)

Spec ==
    /\ Init
    /\ [][Next]_State

=============================================================================