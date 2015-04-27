---------------------------- MODULE AgentRing -----------------------------------
(* An agent circulates on a ring of nodes loaded with tasks and performs a load balancing mission.
   TLC's counterexample to property Test is weird.
*)
EXTENDS Naturals, FiniteSets

CONSTANTS N                   \* the number of nodes in the ring

ASSUME N \in Nat /\ N > 1     \* assume at least 2 nodes

VARIABLES
  Nodes,                      \* the state of the nodes
  Agent,                      \* the state of the agent
  CanCreate                   \* whether nodes can create tasks

vars == <<Nodes, 
          Agent,
          CanCreate>>         \* the state of the system

NodeRange == 0 .. N-1         \* the set of nodes

RightNode(i) == (i+1) % N     \* the node to the right of node i
LeftNode(i) == (i-1) % N      \* the node to the left of node i

--------------------------------------------------------------------------------

AgentState ==
  [ Loc : NodeRange,          \* where (which node) the agent is
    LastLoad : Nat,           \* the load (number of tasks) of the last node visited
    ReadyToMove : BOOLEAN,    \* whether the agent is ready to move to the next node
    Task : 0 .. 1             \* the number of tasks carried by the agent
  ]

NodeState ==
  [ Load : Nat                \* the load of this node
  ]

TypeInv ==
  /\ Nodes \in [ NodeRange -> NodeState ]
  /\ Agent \in AgentState
  /\ CanCreate \in BOOLEAN


SumLoad == 
  LET RECURSIVE Sum(_)
      Sum(n) == IF n = N THEN 0 ELSE Nodes[n].Load + Sum(n+1)
  IN  Sum(0) + Agent.Task

Init == 
  /\ Nodes = [ i \in NodeRange |-> [ Load |-> 0 ] ]
  /\ Agent = [ Loc |-> 0, LastLoad |-> 0, Task |-> 0, ReadyToMove |-> TRUE ]
  /\ CanCreate = TRUE
  /\ TypeInv

--------------------------------------------------------------------------------

Move ==
  /\ Agent.ReadyToMove
  /\ Agent' = [ Agent EXCEPT !.Loc = RightNode(@), !.ReadyToMove = FALSE ]
  /\ UNCHANGED <<Nodes, CanCreate>>
  
LookAndAct ==
  /\ ~Agent.ReadyToMove
  /\ LET Here == Nodes[Agent.Loc].Load
         There == Agent.LastLoad
     IN  IF Here > There /\ Agent.Task = 0 \* pick up one task
         THEN /\ Agent' = [ Agent EXCEPT !.Task = 1, !.LastLoad = Here - 1, !.ReadyToMove = TRUE ]
              /\ Nodes' = [ Nodes EXCEPT ![Agent.Loc].Load = @ - 1 ]
         ELSE IF Here < There /\ Agent.Task = 1 \* drop one task
         THEN /\ Agent' = [ Agent EXCEPT !.Task = 0, !.LastLoad = Here + 1, !.ReadyToMove = TRUE ]
              /\ Nodes' = [ Nodes EXCEPT ![Agent.Loc].Load = @ + 1 ]
         ELSE \* do nothing
              /\ Agent' = [ Agent EXCEPT !.LastLoad = Here, !.ReadyToMove = TRUE ]
              /\ UNCHANGED Nodes
  /\ UNCHANGED CanCreate

Stop ==
  /\ CanCreate' = FALSE
  /\ UNCHANGED <<Nodes, Agent>>

CreateTasks ==
  /\ CanCreate
  /\ \E i \in NodeRange : Nodes' = [ Nodes EXCEPT ![i].Load = @ + N ]
  /\ UNCHANGED <<Agent, CanCreate>>

Next ==
  \/ Move
  \/ LookAndAct
  \/ Stop
  \/ CreateTasks

Prog == Init /\ [][Next]_vars /\ WF_vars(Move) /\ WF_vars(LookAndAct) /\ WF_vars(Stop)

--------------------------------------------------------------------------------

Limits == SumLoad \leq N * N

Test == [](~CanCreate /\ (\A i,j \in NodeRange : Nodes[i].Load = Nodes[j].Load) => [](Agent.Task = 0))

Test2 == [][~CanCreate /\ (\A i,j \in NodeRange : Nodes[i].Load = Nodes[j].Load) => Agent'.Task = 0]_vars
================================================================================