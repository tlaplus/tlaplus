----------------------------- MODULE Consensus ------------------------------ 
EXTENDS Naturals, FiniteSets, TLAPS
CONSTANT Value  
\***** BEGIN TRANSLATION  
VARIABLE chosen

vars == << chosen >>

Init == (* Global variables *)
        /\ chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Value:
             chosen' = {v}

Spec == Init /\ [][Next]_vars

\***** END TRANSLATION
TypeOK == /\ chosen \subseteq Value
          /\ IsFiniteSet(chosen) 

Inv == /\ TypeOK
       /\ Cardinality(chosen) \leq 1

AXIOM EmptySetCardinality == IsFiniteSet({}) /\ Cardinality({}) = 0
AXIOM SingletonCardinality == 
          \A e : IsFiniteSet({e}) /\ (Cardinality({e}) = 1)

SingleCardinalityTest == 
  \A e \in SUBSET {"a", "b", "c"} : IsFiniteSet({e}) /\ (Cardinality({e}) = 1)
LEMMA InductiveInvariance ==
           Inv /\ [Next]_vars => Inv'
<1>1. SUFFICES ASSUME Inv, [Next]_vars
               PROVE  Inv'
  OBVIOUS
<1>2. CASE Next 
  <2>1. PICK v \in Value : chosen' = {v}
    \* In the following BY proof, <1>2 denotes the case assumption Next 
    BY <1>2 DEF Next
  <2>2. QED
    \* In the following BY proof, <1>1 refers to the assumptions
    \* Inv and [Next]_vars
    BY <1>1, <2>1, SingletonCardinality, 1 \leq 1 DEF Inv, TypeOK, Next, vars
<1>4. CASE vars' = vars
  BY <1>1, <1>4 DEF Inv, TypeOK, Next, vars  
<1>5. QED
  BY <1>1, <1>2, <1>4 DEF Next

THEOREM Invariance == Spec => []Inv 
<1>1.  Init => Inv
  BY EmptySetCardinality, 0 \leq 1 DEF Init, Inv, TypeOK

<1>2.  QED
  <2>1. Inv /\ [][Next]_vars => []Inv
    BY InductiveInvariance, PTL
  <2>2. QED
    BY <1>1, <2>1, PTL DEF Spec
LiveSpec == Spec /\ WF_vars(Next)
Success == <>(chosen # {})

ASSUME ValueNonempty == Value # {}

LEMMA EnabledDef ==
        TypeOK => 
          ((ENABLED <<Next>>_vars) <=> (chosen = {}))
<1> DEFINE E == 
       \E chosenp :
               /\ /\ chosen = {}
                  /\ \E v \in Value: chosenp = {v}
               /\ ~ (<<chosenp>> = <<chosen>>)
<1>1. E = ENABLED <<Next>>_vars
  \* BY DEF Next, vars (* and def of ENABLED *)
  PROOF OMITTED
<1>2. SUFFICES ASSUME TypeOK
               PROVE  E = (chosen = {})
  BY <1>1
<1>3. E = \E chosenp : E!(chosenp)!1
  BY <1>2  DEF TypeOK
<1>4. @ = (chosen = {})
 BY <1>2, ValueNonempty DEF TypeOK
<1>5. QED
 BY <1>3, <1>4

THEOREM LiveSpec => Success
<1>1. []Inv /\ [][Next]_vars /\ WF_vars(Next) => (chosen = {} ~> chosen # {})
  <2>1. SUFFICES [][Next]_vars /\ WF_vars(Next) => ((Inv /\ chosen = {}) ~> chosen # {})
     BY PTL \* OBVIOUS (* PTL *)
  <2>2. (Inv /\ (chosen = {})) /\ [Next]_vars => 
                     ((Inv' /\ (chosen = {})') \/ (chosen # {})')
    BY InductiveInvariance
  <2>3. (Inv /\ (chosen = {})) /\ <<Next>>_vars => (chosen # {})'
    BY DEF Inv, Next, vars
  <2>4. (Inv /\ (chosen = {})) => ENABLED <<Next>>_vars
     BY EnabledDef DEF Inv
  <2>5. QED
     BY <2>2, <2>3, <2>4, PTL \* RuleWF1
<1>2. (chosen = {} ~> chosen # {}) => ((chosen = {}) => <>(chosen # {}))
  BY PTL
\*  PROOF OMITTED
<1>3. QED
   BY Invariance, <1>1, <1>2, PTL DEF LiveSpec, Spec, Init, Success (* PTL *)
\*  PROOF OMITTED

THEOREM LiveSpecEquals ==
          LiveSpec <=> Spec /\ ([]<><<Next>>_vars \/ []<>(chosen # {}))
<1>1. /\ Spec <=> Spec /\ []TypeOK
      /\ LiveSpec <=> LiveSpec /\ []TypeOK
  BY Invariance, PTL DEF LiveSpec, Inv (* PTL *)
<1>2. []TypeOK => (([]<>~ENABLED <<Next>>_vars) <=> []<>(chosen # {}))
  \* The introduction of ch is a workaround for a bug in PTL that should
  \* soon be fixed.
  <2> DEFINE ch == chosen # {}
  <2>1. TypeOK => 
          (~(ENABLED <<Next>>_vars) <=> ch)
    BY EnabledDef
   <2> HIDE DEF ch
  <2>2. []TypeOK => []((~ENABLED <<Next>>_vars) <=> ch)
    BY <2>1, PTL (* PTL *)
\*    PROOF OMITTED
  <2>3. QED
    BY <2>2, PTL DEF ch 
\*    PROOF OMITTED
<1>3. QED
 BY <1>1, <1>2, PTL DEF LiveSpec (* and definition of WF *)
\*  PROOF OMITTED
===============================================================================
