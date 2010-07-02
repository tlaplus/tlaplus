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
  [ type : {"every", "some"},
    set  : StateSet ]

Satisfies(stateSet, colorPredicate) ==
  (*************************************************************************)
  (* A set stateSet of states satisfies a color predicate colorPredicate   *)
  (* if the predicate is a good set and EVERY state in stateSet is in that *)
  (* good set, or else it is a bad set and SOME state in stateSet is in    *)
  (* that bad set.                                                         *)
  (*************************************************************************)
  \/ /\ colorPredicate.type = "every"  
     /\ stateSet \subseteq colorPredicate.set
  \/ /\ colorPredicate.type = "some"  
     /\ stateSet \cap colorPredicate.set # {}

THEOREM UnionTheorem ==
  (*************************************************************************)
  (* Asserts that one can compute whether the union of state sets          *)
  (* satisfies a color predicate by knowing whether each of them does.     *)
  (*                                                                       *)
  (* Checked by TLC for a set of 4 model values.                           *)
  (*************************************************************************)
          \A S, T \in StateSet :
             \A pred \in ColorPredicate :
                /\ (pred.type = "every") =>
                      Satisfies(S \cup T, pred) = /\ Satisfies(S, pred)
                                                  /\ Satisfies(T, pred)
                /\ (pred.type = "some") => 
                      Satisfies(S \cup T, pred) = \/ Satisfies(S, pred)
                                                  \/ Satisfies(T, pred)
----------------------------------------------------------------------------
(***************************************************************************)
(* We now show how to represent state sets by bit vectors and how to use   *)
(* the bit vectors to calculate the Satisfies relation for state sets and  *)
(* color predicates.                                                       *)
(***************************************************************************)

VectorDomain  ==  0 .. (Cardinality(State)-1)
CONSTANT StateEnumeration
ASSUME StateEnumerationAssumption == 
       /\ StateEnumeration \in [VectorDomain -> State]
       /\ \A i, j \in VectorDomain :
             (i # j) => (StateEnumeration[i] # StateEnumeration[j])
                
VectorEncoding(stateSet) == 
  [i \in VectorDomain |-> StateEnumeration[i] \in stateSet]
  
And(f, g) == [i \in VectorDomain |-> f[i] /\ g[i]]
ZeroVector == [i \in VectorDomain |-> FALSE]

THEOREM VectorComputation ==
  (*************************************************************************)
  (* How to use bit vectors to compute Satisfies.                          *)
  (*                                                                       *)
  (* Checked by TLC on a set of 4 states and a                             *)
  (*************************************************************************)
          \A S \in StateSet :
            \A pred \in ColorPredicate :
                /\ (pred.type = "every") =>
                      Satisfies(S, pred) = (And(VectorEncoding(S), VectorEncoding(pred.set))
                                              = VectorEncoding(S))
                /\ (pred.type = "some") => 
                      Satisfies(S, pred) = (And(VectorEncoding(S), VectorEncoding(pred.set))
                                              # ZeroVector)


=============================================================================
\* Modification History
\* Last modified Fri Jul 02 09:46:14 PDT 2010 by lamport
\* Created Thu Jul 01 07:55:00 PDT 2010 by lamport
