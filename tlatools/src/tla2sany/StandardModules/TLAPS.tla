------------------------------- MODULE TLAPS --------------------------------

(* Backend pragmas. *)


(***************************************************************************)
(* Each of these pragmas can be cited with a BY or a USE.  The pragma that *)
(* is added to the context of an obligation most recently is the one whose *)
(* effects are triggered.                                                  *)
(***************************************************************************)

(**************************************************************************)
(* Backend pragma: decision procedure for Presburger arithmetic.          *)
(*                                                                        *)
(* Presburger arithmetic consists of first order formulas that use        *)
(* arbitrary logical connectives (\/, /\, TRUE, FALSE, \A, \E), the       *)
(* identity and order relations on the integers (=, #, <, <=, >, >=), the *)
(* integer valued operators + and - (including unary -), and              *)
(* multiplication by integer constants.                                   *)
(**************************************************************************)
THEOREM SimpleArithmetic == TRUE (*{ by (cooper) }*)


(***************************************************************************)
(* The following theorem tells the prover to use the law of set            *)
(* extensionality, which can be written as                                 *)
(*                                                                         *)
(*    THEOREM  \A S, T : (S = T) <=> (\A x : (x \in S) <=> (x \in t))      *)
(*                                                                         *)
(* Defining SetExtensionality to equal this formula would cause TLAPS to   *)
(* add this formula to the set of hypotheses it gives the back end         *)
(* provers whenever SetExtensionality is used.  Since the pragma tells     *)
(* the Isabelle back end to use this rule, adding it to the set of         *)
(* hypotheses would be redundant and make Isabelle do unnecessary work in  *)
(* trying to prove the goal.                                               *)
(***************************************************************************)
THEOREM SetExtensionality == TRUE 
           (*{ by (isabelle "(auto intro: setEqualI)")}*)

(***************************************************************************)
(* The following axiom is needed to deduce NotInSetS \notin SetS from the  *)
(* definition                                                              *)
(*                                                                         *)
(*   NotInSetS == CHOOSE v : v \notin SetS                                 *)
(***************************************************************************)
AXIOM NoSetContainsEverything == \A S : \E x : x \notin S
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following pragmas should be used only as a last resource.  They are *)
(* dependent upon the particular backend provers, and are unlikely to have *)
(* any effect if the set of backend provers changes.  Moreover, they are   *)
(* meaningless to a reader of the proof.                                   *)
(***************************************************************************)

(***********************************************************************)
(* Backend pragmas: Zenon with much longer timeouts                    *)
(*                                                                     *)
(* These pragmas increase the timeout for Zenon (which is 5 seconds by *)
(* default) by factors of 2.                                           *)
(***********************************************************************)
THEOREM SlowZenon     == TRUE (*{ by (zenon 10) }*)
THEOREM SlowerZenon   == TRUE (*{ by (zenon 20) }*)
THEOREM VerySlowZenon == TRUE (*{ by (zenon 40) }*)
THEOREM SlowestZenon  == TRUE (*{ by (zenon 80) }*)

(********************************************************************)
(* Backend pragma: Isabelle's automatic search ("auto")             *)
(*                                                                  *)
(* This pragma bypasses Zenon. It is useful in situations involving *)
(* essentially simplification and equational reasoning.             *)
(********************************************************************)
THEOREM Auto == TRUE (*{ by (isabelle "auto") }*)

(********************************************************************)
(* Backend pragma: Isabelle's "force" tactic                        *)
(*                                                                  *)
(* This pragma bypasses Zenon. It is useful in situations involving *)
(* quantifier reasoning.                                            *)
(********************************************************************)
THEOREM Force == TRUE (*{ by (isabelle "force") }*)

(***********************************************************************)
(* Backend pragma: Isabelle's "simplification" tactics                 *)
(*                                                                     *)
(* These tactics simplify the goal before running one of the automated *)
(* tactics. They are often necessary for obligations involving record  *)
(* or tuple projections. Use the SimplfyAndSolve tactic unless you're  *)
(* sure you can get away with just Simplification                      *)
(***********************************************************************)
THEOREM SimplifyAndSolve == TRUE (*{ by (isabelle "clarsimp auto?") }*)
THEOREM Simplification == TRUE (*{ by (isabelle "clarsimp") }*)

(**************************************************************************)
(* Backend pragma: Isabelle's tableau prover ("blast")                    *)
(*                                                                        *)
(* This pragma bypasses Zenon and uses Isabelle's built-in theorem        *)
(* prover, Blast. It is almost never better than Zenon by itself, but     *)
(* becomes very useful in combination with the Auto pragma above. The     *)
(* AutoBlast pragma first attempts Auto and then uses Blast to prove what *)
(* Auto could not prove. (There is currently no way to use Zenon on the   *)
(* results left over from Auto.)                                          *)
(**************************************************************************)
THEOREM Blast     == TRUE (*{ by (isabelle "blast") }*)
THEOREM AutoBlast == TRUE (*{ by (isabelle "auto, blast") }*)
----------------------------------------------------------------------------
(***************************************************************************)
(*                           TEMPORAL LOGIC                                *)
(*                                                                         *)
(* The following rules are intended to be used when TLAPS handles temporal *)
(* logic.  They will not work now.  Moreover when temporal reasoning is    *)
(* implemented, these rules may be changed or omitted, and additional      *)
(* rules will probably be added.  However, they are included mainly so     *)
(* their names will be defined, preventing the use of identifiers that are *)
(* likely to produce name clashes with future versions of this module.     *)
(***************************************************************************)


(***************************************************************************)
(* The following proof rules (and their names) are from the paper "The     *)
(* Temporal Logic of Actions".                                             *)
(***************************************************************************)
THEOREM RuleTLA1 == ASSUME STATE P, STATE f,
                           P /\ (f' = f) => P'
                    PROVE  []P <=> P /\ [][P => P']_f

THEOREM RuleTLA2 == ASSUME STATE P, STATE Q, STATE f, STATE g,
                           ACTION A, ACTION B,
                           P /\ [A]_f => Q /\ [B]_g
                    PROVE  []P /\ [][A]_f => []Q /\ [][B]_g

THEOREM RuleINV1 == ASSUME STATE I, STATE F,  ACTION N,
                           I /\ [N]_F => I'
                    PROVE  I /\ [][N]_F => []I

THEOREM RuleINV2 == ASSUME STATE I, STATE f, ACTION N
                   PROVE  []I => ([][N]_f <=> [][N /\ I /\ I']_f)

THEOREM RuleWF1 == ASSUME STATE P, STATE Q, STATE f, ACTION N, ACTION A,
                          P /\ [N]_f => (P' \/ Q'),
                          P /\ <<N /\ A>>_f => Q',
                          P => ENABLED <<A>>_f
                   PROVE  [][N]_f /\ WF_f(A) => (P ~> Q)

THEOREM RuleSF1 == ASSUME STATE P, STATE Q, STATE f, 
                          ACTION N, ACTION A, TEMPORAL F,
                          P /\ [N]_f => (P' \/ Q'),
                          P /\ <<N /\ A>>_f => Q',
                          []P /\ [][N]_f /\ []F => <> ENABLED <<A>>_f
                   PROVE  [][N]_f /\ SF_f(A) /\ []F => (P ~> Q)

(***************************************************************************)
(* The rules WF2 and SF2 in "The Temporal Logic of Actions" are obtained   *)
(* from the following two rules by the following substitutions: `.         *)
(*                                                                         *)
(*          ___        ___         _______________                         *)
(*      M <- M ,   g <- g ,  EM <- ENABLED <<M>>_g       .'                *)
(***************************************************************************)
THEOREM RuleWF2 == ASSUME STATE P, STATE f, STATE g, STATE EM,
                          ACTION A, ACTION B, ACTION N, ACTION M,
                          TEMPORAL F,
                          <<N /\ B>>_f => <<M>>_g,
                          P /\ P' /\ <<N /\ A>>_f /\ EM => B,
                          P /\ EM => ENABLED A,
                          [][N /\ ~B]_f /\ WF_f(A) /\ []F /\ <>[]EM => <>[]P
                   PROVE  [][N]_f /\ WF_f(A) /\ []F => []<><<B>>_g \/ []<>(~EM)

THEOREM RuleSF2 == ASSUME STATE P, STATE f, STATE g, STATE EM,
                          ACTION A, ACTION B, ACTION N, ACTION M,
                          TEMPORAL F,
                          <<N /\ B>>_f => <<M>>_g,
                          P /\ P' /\ <<N /\ A>>_f /\ EM => B,
                          P /\ EM => ENABLED A,
                          [][N /\ ~B]_f /\ SF_f(A) /\ []F /\ []<>EM => <>[]P
                   PROVE  [][N]_f /\ SF_f(A) /\ []F => []<><<B>>_g \/ <>[](~EM)


(***************************************************************************)
(* The following rule is a special case of the general temporal logic      *)
(* proof rule STL4 from the paper "The Temporal Logic of Actions".  The    *)
(* general rule is for arbitrary temporal formulas F and G, but it cannot  *)
(* yet be handled by TLAPS.                                                *)
(***************************************************************************)
THEOREM RuleInvImplication ==
  ASSUME STATE F, STATE G,
         F => G
  PROVE  []F => []G
PROOF OMITTED

(***************************************************************************)
(* The following rule is a special case of rule TLA2 from the paper "The   *)
(* Temporal Logic of Actions".                                             *)
(***************************************************************************)
THEOREM RuleStepSimulation ==
  ASSUME STATE I, STATE f, STATE g,
         ACTION M, ACTION N,
         I /\ I' /\ [M]_f => [N]_g
  PROVE  []I /\ [][M]_f => [][N]_g
PROOF OMITTED

(***************************************************************************)
(* The following may be used to invoke a decision procedure for            *)
(* propositional temporal logic.                                           *)
(***************************************************************************)
THEOREM PropositionalTemporalLogic == TRUE
=============================================================================

