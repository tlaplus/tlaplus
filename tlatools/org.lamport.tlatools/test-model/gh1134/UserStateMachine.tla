------------------------------- MODULE UserStateMachine -------------------------------

EXTENDS Sequences

VARIABLE State

Init(userIDs) ==
    State = [u \in userIDs |-> "INIT"]
    
Next(user) ==
    State' = [State EXCEPT ![user] = "DONE"]

=============================================================================

Before param refinement:
[State line 5, col 10 to line 5, col 14 of module UserStateMachine->(2 :> "INIT"), 
    userIDs line 7, col 6 to line 7, col 12 of module UserStateMachine-><LAZY line 13, col 27 to line 13, col 33 of module SingleUser>, 
        State line 6, col 10 to line 6, col 14 of module Base->(2 :> "INIT"), 
            UserIDs line 5, col 10 to line 5, col 16 of module Base-><LAZY line 6, col 28 to line 6, col 30 of module MultiUser>]

With param refinement:
[State line 5, col 10 to line 5, col 14 of module UserStateMachine->(2 :> "INIT"), 
    State line 6, col 10 to line 6, col 14 of module Base->(2 :> "INIT"), 
        UserIDs line 5, col 10 to line 5, col 16 of module Base-><LAZY line 6, col 28 to line 6, col 30 of module MultiUser>, 
            userIDs line 7, col 6 to line 7, col 12 of module UserStateMachine-><LAZY line 13, col 27 to line 13, col 33 of module SingleUser>]

