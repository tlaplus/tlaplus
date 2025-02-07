------------------------------- MODULE Base -------------------------------

EXTENDS FiniteSets, Integers, TLC

CONSTANT UserIDs
VARIABLE State

StateMachine == INSTANCE UserStateMachine

=============================================================================