The Toolbox will provide LOGICAL COLORS, numbered from 1 through
NumberOfStepColors, with which a theorem or proof step can be colored.
(The preference menu allows the user to assign physical colors to
these logical colors.)  Each logical color has a COLOR PREDICATE.  The
logical color of a step is the lowest-numbered logical color whose
color predicate is true.  (If none are true, the step is not colored.)

A PROOF TREE consists of a theorem or proof step (the ROOT) together
with its proof (which may be empty).  A non-LEAF proof tree is one
whose root's proof is a sequence of proof trees.  A LEAF proof tree is
one whose whose root either has no proof or has a leaf proof.  Each
leaf proof tree has zero or more proof OBLIGATIONS. For convenience,
we define a leaf proof whose root step can take a proof but for which
that proof is either missing or OMITTED to contain a single DUMMY
obligation.  The obligations of a proof tree are defined in the
obvious way to be the set of all obligations of all leaf proof tree in
the proof tree.

At any time, each obligation has a STATE. For a dummy obligation, the
status is either `missing' or `omitted'.  For an ordinary proof
obligation, that state consists of a STATUS for each prover.
Currently, there are three provers with the following possible
statuses:

 1. Isabelle:  untried, proving, proved, failed, stopped
 2. Other:     untried, proving, proved, failed, stopped
 3. TLAPM:     none, trivial

For now, "Other" includes Zenon, the Cooper algorithm, and any SMT
backend.  The state of an ordinary obligation is written as a triple
such as <<proving, failed, none>>, where the value of the i-th element
is the obligation's proof status for the i-th prover.

A color predicate is specified by three things:

 - A OS set of obligation states.
 - Whether it is an `every' or a `some' predicate.
 - Whether or not it is a `leaf' predicate.

A color predicate has the following boolean value for a proof tree.

  /\ \/ /\ It is an `every' predicate
        /\ The state of every obligation in the proof tree is
           in OS.
     \/ /\ It is a `some' predicate
        /\ The state of some obligation in the proof tree is
           in OS.
  /\ \/ It is not a `leaf' predicate
     \/ The proof tree is a leaf proof tree

A color predicate is specified by a string with the following syntax

   <color-predicate> ::=  ["leaf"]?  ["every" | "some"] <state-set>*

   <state-set> ::= "missing" | "omitted" 
                     | "(" <statuses> "," <statuses> "," <statuses> ")"

   <statuses> ::=  <status>* | "-" <status>+ 

Each <state-set> specifies a set of states, and a sequence of
<state-sets>s specifies their union.  The <state-set>s "missing" and
"omitted" specify the obvious singleton sets of dummy-obligation
states.  A <statuses> specifies a set of possible proofs statuses is
specified by a list, where "-" means `all statuses except' and the
empty list means all possible statuses.

A triple of sequences of statuses specifies the set of all
states in which the proof status of the i-th prover is one of the
statuses in the i-th component of the triple.  An empty sequence
of statuses is an abbreviation for all possible statuses.
For example, the <state-set>

   (proving proved, untried, ) 

is the set of all obligation states in which Isabelle's proof status
is either proving or proved, the `Other' prover's status is untried,
and TLAPM's prover status is either none or trivial.  For example,

   every missing omitted ( , , )

is a predicate that is always true and

   leaf every missing omitted ( , , )

is true of a proof tree iff it is a leaf proof.  The color predicate

   some

is false for every proof tree.  The predicate

   every omitted (proved, , ) (, proved, ) (, , trivial)

is true iff every obligation is either omitted, is proved by Isabelle
or the Other prover, or is found trivial by TLAPM. The predicate

  leaf some (failed, - proved, none) (- proved, failed, none)

is true for a leaf node if, for some obligation, one of Isabelle's and
the Other prover's status is failed, and the other one's status is not
proved, and TLAPM has not found it to be trivial.

----------------------------------------------------------------------------
The following spec shows how all the information needed to specify
provers and their statuses can be provided in one array of array of strings.
(Since this is TLA+, I use sequences instead of arrays.)  

The main module contains the definitions for obligation states.  The
instantiated module ColorPredicates explains how a color predicate is
represented using a bit vector plus an indication of whether it is an
"every" or "some" predicate.  The spec ignores the distinction between 
leaf and non-leaf color predicates.


---------------------------- MODULE ProofStatus ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* ProofStatesSpec[i] is the sequence of possible statuses (which are      *)
(* strings) for prover i.                                                  *)
(***************************************************************************)
CONSTANT ProofStatesSpec  
ASSUME ConstantAssumps ==  ProofStatesSpec \in Seq(Seq(STRING))

NumberOfProvers == Len(ProofStatesSpec)
  
StatusesOfProver(i) == 
  (*************************************************************************)
  (* The set of possible statuses of prover i.                             *)
  (*************************************************************************)
  { ProofStatesSpec[i][j] : j \in 1..Len(ProofStatesSpec[i]) }

Statuses == 
  (*************************************************************************)
  (* The set of all possible statuses of all provers.                      *)
  (*************************************************************************)
  UNION {StatusesOfProver(i) : i \in 1..NumberOfProvers}                       
                         
ObligationState == 
  (*************************************************************************)
  (* The set of all possible obligation states.                            *)
  (*************************************************************************)
    [ type : {"missing", "omitted"} ]
  \cup
    { s \in [ type : {"proof"},
              status : [1..NumberOfProvers -> Statuses]] :
        \A i \in 1..NumberOfProvers : s.status[i] \in StatusesOfProver(i) }
(***************************************************************************)
(* We define Sum(f) and Product(f) to be the sum and product of f[i] for   *)
(* all i in the domain of the function f.                                  *)
(***************************************************************************)
RECURSIVE Sum(_), Product(_)
Sum(f) == IF DOMAIN f = {} 
            THEN 0
            ELSE LET i == CHOOSE v \in DOMAIN f : TRUE
                 IN  f[i] + Sum([j \in (DOMAIN f) \ {i} |-> f[j]])
Product(f) == IF DOMAIN f = {} 
                THEN 1
                ELSE LET i == CHOOSE v \in DOMAIN f : TRUE
                     IN  f[i] * Product([j \in (DOMAIN f) \ {i} |-> f[j]])

(***************************************************************************)
(* The StateNumber operator assigns distinct, consecutive numbers starting *)
(* from 0 to all obligation states minus.                                  *)
(***************************************************************************)
StateNumber(s) == 
  CASE s.type = "missing" -> 0
    [] s.type = "omitted" -> 1
    [] s.type = "proof" ->
         2 + Sum( [ i \in 1..NumberOfProvers |->
                    ((CHOOSE j \in 1..Len(ProofStatesSpec[i]) : 
                               ProofStatesSpec[i][j] = s.status[i]) - 1)
                     * Product( [ k \in 1..(i-1) |-> Len(ProofStatesSpec[k])
                                 ] )
                  ] )
                  
THEOREM IsNumbering == 
         /\ \A s \in ObligationState : 
              StateNumber(s) \in 0..(Cardinality(ObligationState)-1)
         /\ \A s, t \in ObligationState : s # t => StateNumber(s) # StateNumber(t)

(***************************************************************************)
(* NumberToState would be the inverse of StateNumber if StateNumber had    *)
(* been defined to be a function on states rather than an operator.        *)
(***************************************************************************)
NumberToState[i \in 0..(Cardinality(ObligationState)-1)] == 
   CHOOSE s \in ObligationState : PrintT(s) /\ StateNumber(s) = i

(***************************************************************************)
(* We instantiate the ColorPredicates module which describes color         *)
(* predicates for an arbitrary set of obligation states and an enumeration *)
(* of them.                                                                *)
(***************************************************************************)
INSTANCE ColorPredicates WITH State <- ObligationState, 
                              StateEnumeration <- NumberToState
============================================================================
\* Modification History
\* Last modified Fri Jul 02 09:23:06 PDT 2010 by lamport
\* Created Wed Jun 30 01:51:58 PDT 2010 by lamport
