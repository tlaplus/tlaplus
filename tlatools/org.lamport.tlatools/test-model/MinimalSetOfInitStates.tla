--------- MODULE MinimalSetOfInitStates ------------
VARIABLE x

\* x = 0 true because _second_ conjunct is true.
\* The allAssigned branch in Tool#getInitStates(ActionItemList, TLCState, IStateFunctor)
\* prevents TLC from generating three states with x = 0.  
I1a == /\ x = 0
       /\ \/ 1 = 1
          \/ 2 = 2
          \/ 3 = 3
         
\* x = 1 true because _first_ conjunct is true.
\* The allAssigned branch in Tool#getInitStates(ActionItemList, TLCState, IStateFunctor)
\* _does not_ prevents TLC from generating three states with x = 1.
I1b == /\ \/ 1 = 1
          \/ 2 = 2
          \/ 3 = 3
       /\ x = 1

\* x = 2 true because _first_ conjunct is true.
\* The allAssigned branch in Tool#getInitStates(ActionItemList, TLCState, IStateFunctor)
\* _does not_ prevents TLC from generating three states with x = 2. The "~~" trick prevents
\* TLC from generating three states with x = 2 because the default case in Tool line 729
\* simply evaluates the first conjunct without generating states.
I1c == /\ ~~(\/ 1 = 1
             \/ 2 = 2
             \/ 3 = 3)
       /\ x = 2
       
\* Doesn't assign 1 bc pred is false, thus not counted as init.
I2 == /\ x = 3 
      /\ \/ 1 = 2
         \/ 2 = 3
         \/ 3 = 1

\* Doesn't assign 1 because pred is false,
\* but counted as init because pred comes first.
I3 == /\ \/ 1 = 2
         \/ 2 = 3
         \/ 3 = 1
      /\ x = 4

I4 == \/ x = 5
      \/ x = 6
        /\ \/ \/ 1 = 2
              \/ 1 = 1 
           \/ 2 = 3
           \/ 3 = 2

I5 == /\ x = 7

Init == \/ I1a
        \/ I1b
        \/ I1c
        \/ I2
        \/ I3
        \/ I4
        \/ I5
           

Next == UNCHANGED x
====================================================
