-------------------------- MODULE ColorPredicates --------------------------
EXTENDS Naturals, FiniteSets

CONSTANT State
ASSUME IsFiniteSet(State)

StateSet == SUBSET State

ColorPredicate == 
  (*************************************************************************)
  (* A color predicate is a set of states that is either a "good" set or a *)
  (* "bad" set.                                                            *)
  (*************************************************************************)
  [ type : {"GoodSet", "BadSet"},
    set  : StateSet ]

Satisfies(stateSet, colorPredicate) ==
  (*************************************************************************)
  (* A set stateSet of states satisfies a color predicate colorPredicate   *)
  (* if the predicate is a good set and EVERY state in stateSet is in that *)
  (* good set, or else it is a bad set and SOME state in stateSet is in    *)
  (* that bad set.                                                         *)
  (*************************************************************************)
  \/ /\ colorPredicate.type = "GoodSet"  
     /\ stateSet \subseteq colorPredicate.set
  \/ /\ colorPredicate.type = "BadSet"  
     /\ stateSet \cap colorPredicate.set # {}

THEOREM UnionTheorem ==
  (*************************************************************************)
  (* Asserts that one can compute whether the union of state sets          *)
  (* satisfies a color predicate by knowing whether each of them does.     *)
  (*************************************************************************)
          \A S, T \in StateSet :
             \A pred \in ColorPredicate :
                /\ (pred.type = "GoodSet") =>
                      Satisfies(S \cup T, pred) = /\ Satisfies(S, pred)
                                                  /\ Satisfies(T, pred)
                /\ (pred.type = "BadSet") => 
                      Satisfies(S \cup T, pred) = \/ Satisfies(S, pred)
                                                  \/ Satisfies(T, pred)
----------------------------------------------------------------------------
VectorDomain  ==  0 .. (Cardinality(State)-1)
CONSTANT StateEnumeration
ASSUME /\ StateEnumeration \in [VectorDomain -> State]
       /\ \A i, j \in VectorDomain :
             (i # j) => (StateEnumeration[i] # StateEnumeration[j])
                
VectorEncoding(stateSet) == 
  [i \in VectorDomain |-> StateEnumeration[i] \in stateSet]
  
And(f, g) == [i \in VectorDomain |-> f[i] /\ g[i]]
ZeroVector == [i \in VectorDomain |-> FALSE]

THEOREM VectorComputation ==
          \A S \in StateSet :
            \A pred \in ColorPredicate :
                /\ (pred.type = "GoodSet") =>
                      Satisfies(S, pred) = (And(VectorEncoding(S), VectorEncoding(pred.set))
                                              = VectorEncoding(S))
                /\ (pred.type = "BadSet") => 
                      Satisfies(S, pred) = (And(VectorEncoding(S), VectorEncoding(pred.set))
                                              # ZeroVector)

=============================================================================
\* Modification History
\* Last modified Thu Jul 01 08:45:11 PDT 2010 by lamport
\* Created Thu Jul 01 07:55:00 PDT 2010 by lamport
