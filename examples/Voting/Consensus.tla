----------------------------- MODULE Consensus ------------------------------ 
EXTENDS Naturals, Sets

CONSTANT Value

VARIABLE chosen

Init == chosen = {}
Next == /\ chosen = {}
        /\ \E v \in Value : chosen' = {v}
Spec == Init /\ [][Next]_chosen 

-----------------------------------------------------------------------------

Inv == /\ chosen \subseteq Value
       /\ IsFiniteSet(chosen) 
       /\ Cardinality(chosen) \leq 1

-----------------------------------------------------------------------------

THEOREM Invariance == Spec => []Inv

<1>1 Init => Inv
    <2>1 0 \leq 1 PROOF OBVIOUS 
    <2>2 QED PROOF BY <2>1, CardinalityZero DEF Init, Inv

<1>2 Inv /\ [Next]_chosen => Inv'
    <2>1 SUFFICES ASSUME Inv, [Next]_chosen
                  PROVE  Inv'
         PROOF OBVIOUS
    <2>2 SUFFICES /\ chosen' \subseteq Value
                  /\ IsFiniteSet(chosen')
                  /\ Cardinality(chosen') \leq 1
         PROOF BY DEF Inv, IsFiniteSet, IsBijection
    <2>3 USE DEF Inv, Next
    <2>4 CASE UNCHANGED chosen PROOF BY DEF IsFiniteSet
    <2>5 CASE Next
          <3>1 1 \leq 1 PROOF OBVIOUS
          <3>2 PICK v \in Value : chosen' = {v} PROOF OBVIOUS
          <3>3 /\ Cardinality({v}) \leq 1
               /\ IsFiniteSet({v})
               PROOF BY <3>1, CardinalityOne
          <3>4 QED PROOF BY <3>1, <3>2, <3>3
 
    <2>6 QED PROOF BY <2>4, <2>5

<1>3 QED PROOF OMITTED

=============================================================================

