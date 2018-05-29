--------- MODULE MinimalSetOfNextStates ------------
VARIABLE x

Init == x = 42


\* x = 0 true because _second_ conjunct is true.
\* The allAssigned branch in Tool#getInitStates(ActionItemList, TLCState, IStateFunctor)
\* prevents TLC from generating duplicate states with x = 0.  
N1a == /\ x' = 0
       /\ \/ 1 = 1
          \/ 2 = 2
          \/ 3 = 3
         
\* x = 1 true because _first_ conjunct is true.
\* The allAssigned branch in Tool#getInitStates(ActionItemList, TLCState, IStateFunctor)
\* _does not_ prevents TLC from generating duplicate states with x = 1.
N1b == /\ \/ 1 = 1
          \/ 2 = 2
          \/ 3 = 3
       /\ x' = 1

\* x = 2 true because _first_ conjunct is true.
\* The allAssigned branch in Tool#getInitStates(ActionItemList, TLCState, IStateFunctor)
\* _does not_ prevents TLC from generating three states with x = 2. The "~~" trick prevents
\* TLC from generating duplicate states with x = 2 because Tool simply evaluates the first
\* conjunct without generating states.
N1c == /\ ~~(\/ 1 = 1
             \/ 2 = 2
             \/ 3 = 3)
       /\ x' = 2
       
N2 == /\ x' = 3 \* Pred FALSE
      /\ \/ 1 = 2
         \/ 2 = 3
         \/ 3 = 1

N3 == /\ \/ 1 = 2 \* Pred FALSE
         \/ 2 = 3
         \/ 3 = 1
      /\ x' = 4

N4 == \/ x' = 5
      \/ x' = 6
        /\ \/ \/ 1 = 2
              \/ 1 = 1 
           \/ 2 = 3
           \/ 3 = 2

N5 == /\ x' = 7

Next == \/ N1a
        \/ N1b
        \/ N1c
        \/ N2
        \/ N3
        \/ N4
        \/ N5
           
Inv == x \in {42,0,1,2,5,6,7}
====================================================
