---------------------------- MODULE ProofStatus ----------------------------
(***************************************************************************)
(* We specify a way of presenting proof status information to the user by  *)
(* coloring proof steps.  This is done by defining a step-color predicate  *)
(* to be a predicate on a proof, where a proof consists of a step or       *)
(* theorem together with its proof, which may be missing or OMITTED.       *)
(*                                                                         *)
(* Step-color predicates can be specified to apply either to any proof or  *)
(* only to leaf proofs (proofs steps that do not contain a proof with      *)
(* lower-level proof steps).  In the latter case, they equal false on      *)
(* non-leaf proof steps.                                                   *)
(*                                                                         *)
(* The Toolbox will have a fixed set of colors, numbered from 1 to N.  A   *)
(* coloring is specified by assigning a step-color predicate to each       *)
(* color.  A step is colored with the highest-numbered color whose         *)
(* step-color predicate is true.                                           *)
(***************************************************************************)

EXTENDS Naturals, Sequences

(***************************************************************************)
(*                         PROOF OBLIGATION STATUSES                       *)
(*                                                                         *)
(* We define a possible proof-obligation status to be a function from      *)
(* provers to outcomes.                                                    *)
(***************************************************************************)

Prover == {"tlapm",  "primary", "auxiliary"}
    (***********************************************************************)
    (* The set of all back-end provers.  The three values currently stand  *)
    (* for `trivial', Isabelle, and any back-end besides Isabelle.         *)
    (***********************************************************************)
    
ProofOutcome == {"untried", "failed", "proved", "stopped", "being_proved"}

Omitted == CHOOSE v : v \notin [Prover -> ProofOutcome]
Missing == CHOOSE v : v \notin [Prover -> ProofOutcome] \cup {Omitted}
ObligationStatus == { f \in [Prover -> ProofOutcome] :
                         f["tlapm"] \in {"untried", "proved"} } 
                    \cup {Omitted, Missing}     
  (*************************************************************************)
  (* The set of all possible statuses for an obligation, where a status    *)
  (* consists of either an outcome from each prover or a special value     *)
  (* indicating that the obligation is a dummy one representing an omitted *)
  (* or missing proof.                                                     *)
  (*************************************************************************)
----------------------------------------------------------------------------
(***************************************************************************)
(*                        PROOF-STATUS TREES                               *)
(*                                                                         *)
(* We define an abstract proof tree that represents a step or theorem and  *)
(* proof statuses of all its obligations.                                  *)
(***************************************************************************)

CONSTANTS Obligation
  (*************************************************************************)
  (* We assume uninterpreted sets of obligations.                          *)
  (*************************************************************************)

ProofTree ==
  (*************************************************************************)
  (* An abstract representation of a theorem or proof step and its proof.  *)
  (* This uses a standard TLA+ recursive definition of this sort of tree,  *)
  (* where P[0] is the set of steps with a (possibly missing or omitted)   *)
  (* leaf proof, and Pf[n] is the set of all proof trees of depth at most  *)
  (* n.                                                                    *)
  (*                                                                       *)
  (* A proof step that does not take a proof is considered to have a leaf  *)
  (* proof.  The leaf proof has obligations iff the step generates         *)
  (* obligations.  A missing or omitted proof is represented by a single   *)
  (* obligation whose status is Missing or Omitted.                        *)
  (*************************************************************************)
  LET Pf[n \in Nat] == 
        IF n = 0 THEN [ leafProof     : TRUE,
                        obligations   : SUBSET Obligation ]
                 ELSE [ leafProof : FALSE,
                        children  : Seq(Pf[n-1]) ]
                      \cup Pf[n-1]
  IN  UNION {Pf[n] : n \in Nat}          
----------------------------------------------------------------------------
(***************************************************************************)
(*                          STATUS SPECIFICATIONS                          *)
(***************************************************************************)
CONSTANT ObligationStatuses
ASSUME ObligationStatuses \in [Obligation -> ObligationStatuses]

ObligationPredicate == [ObligationStatus -> BOOLEAN] 

RECURSIVE Apply(_, _)
Apply(obPred, pfTree) ==
  (*************************************************************************)
  (* Defines the result of applying an obligation predicate to a proof     *)
  (* tree, where obPred is true of pfTree iff it is true of some           *)
  (* obligation in pfTree.                                                 *)
  (*************************************************************************)
  IF pfTree.leaf THEN \E ob \in pfTree.obligations : 
                         obPred[ObligationStatus[ob]] = TRUE
                 ELSE \E ch \in pfTree.children : Apply(obPred, ch)

Disjunction(f, g) == [o \in Obligation |-> f[o] \/ g[o]]
THEOREM \A f, g \in ObligationPredicate, pfTree \in ProofTree :
          Apply(Disjunction(f, g), pfTree) = 
             Apply(f, pfTree) \/ Apply(g, pfTree)

\*StepColorPredicate == SUBSET LeafStepStatus
  (*************************************************************************)
  (* A predicate (represented as a set) on leaf-proof tree statuses.  Note *)
  (* that the cardinality of StepColorPredicate is greater than            *)
  (* 2 ^ (2 ^ Cardinality(ObligationStatus)).                              *)
  (*************************************************************************)

-----------------------------------------------------------------------------
(***************************************************************************
                     IMPLEMENTING STEP-COLOR PREDICATES
                     
Assume that Prover consists of two elements.  Then an element of ObligationStatus
is a subset of a set containing 10 elements, so it can be specified by 10 bits.  A LeafStepStatus is essentially either "missing", "OMITTED", or else an element 
of SUBSET ObligationStatus.  Any step-color predicate that one is likely
to want to use should be easily represented by a very small boolean combination
of leaf-step statuses.  For example, 

   Steps for which 
coloring steps for which a proof is found

For a positive boolean combination, the current algorithms for 
 ***************************************************************************)


=============================================================================
\* Modification History
\* Last modified Thu Jul 01 01:41:20 PDT 2010 by lamport
\* Created Wed Jun 30 01:51:58 PDT 2010 by lamport
