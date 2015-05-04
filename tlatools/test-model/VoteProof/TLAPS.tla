------------------------------- MODULE TLAPS --------------------------------

(* Backend pragmas. *)


(***************************************************************************)
(* Each of these pragmas can be cited with a BY or a USE.  The pragma that *)
(* is added to the context of an obligation most recently is the one whose *)
(* effects are triggered.                                                  *)
(***************************************************************************)

(***************************************************************************)
(* The following pragmas should be used only as a last resource.  They are *)
(* dependent upon the particular backend provers, and are unlikely to have *)
(* any effect if the set of backend provers changes.  Moreover, they are   *)
(* meaningless to a reader of the proof.                                   *)
(***************************************************************************)


(**************************************************************************)
(* Backend pragma: use the SMT solver for arithmetic.                     *)
(*                                                                        *)
(* This method exists under this name for historical reasons.             *)
(**************************************************************************)

SimpleArithmetic == TRUE (*{ by (prover:"smt3") }*)


(**************************************************************************)
(* Backend pragma: SMT solver                                             *)
(*                                                                        *)
(* This method translates the proof obligation to SMTLIB2. The supported  *)
(* fragment includes first-order logic, set theory, functions and         *)
(* records.                                                               *)
(* SMT calls the smt-solver with the default timeout of 5 seconds         *)
(* while SMTT(n) calls the smt-solver with a timeout of n seconds.        *)
(**************************************************************************)

SMT == TRUE (*{ by (prover:"smt3") }*)
SMTT(X) == TRUE (*{ by (prover:"smt3"; timeout:@) }*)


(**************************************************************************)
(* Backend pragma: CVC3 SMT solver                                        *)
(*                                                                        *)
(* CVC3 is used by default but you can also explicitly call it.           *)
(**************************************************************************)

CVC3 == TRUE (*{ by (prover: "cvc33") }*)
CVC3T(X) == TRUE (*{ by (prover:"cvc33"; timeout:@) }*)

(**************************************************************************)
(* Backend pragma: Yices SMT solver                                       *)
(*                                                                        *)
(* This method translates the proof obligation to Yices native language.  *)
(**************************************************************************)

Yices == TRUE (*{ by (prover: "yices3") }*)
YicesT(X) == TRUE (*{ by (prover:"yices3"; timeout:@) }*)

(**************************************************************************)
(* Backend pragma: veriT SMT solver                                       *)
(*                                                                        *)
(* This method translates the proof obligation to SMTLIB2 and calls veriT.*)
(**************************************************************************)

veriT == TRUE (*{ by (prover: "verit") }*)
veriTT(X) == TRUE (*{ by (prover:"verit"; timeout:@) }*)

(**************************************************************************)
(* Backend pragma: Z3 SMT solver                                          *)
(*                                                                        *)
(* This method translates the proof obligation to SMTLIB2 and calls Z3.   *)
(**************************************************************************)

Z3 == TRUE (*{ by (prover: "z33") }*)
Z3T(X) == TRUE (*{ by (prover:"z33"; timeout:@) }*)

(**************************************************************************)
(* Backend pragma: SPASS superposition prover                             *)
(*                                                                        *)
(* This method translates the proof obligation to the DFG format language *)
(* supported by the ATP SPASS. The translation is based on the SMT one.   *)
(**************************************************************************)

Spass == TRUE (*{ by (prover: "spass") }*)
SpassT(X) == TRUE (*{ by (prover:"spass"; timeout:@) }*)

(**************************************************************************)
(* Backend pragma: The PTL propositional linear time temporal logic       *)
(* prover.  It currently is the LS4 backend.                              *)
(*                                                                        *)
(* This method translates the negetation of the proof obligation to       *)
(* Seperated Normal Form (TRP++ format) and checks for unsatisfiability   *)
(**************************************************************************)

LS4 == TRUE (*{ by (prover: "ls4") }*)
PTL == TRUE (*{ by (prover: "ls4") }*)

(**************************************************************************)
(* Backend pragma: Zenon with different timeouts (default is 10 seconds)  *)
(*                                                                        *)
(**************************************************************************)

Zenon == TRUE (*{ by (prover:"zenon") }*)
ZenonT(X) == TRUE (*{ by (prover:"zenon"; timeout:@) }*)

(********************************************************************)
(* Backend pragma: Isabelle with different timeouts and tactics     *)
(*  (default is 30 seconds/auto)                                    *)
(********************************************************************)

Isa == TRUE (*{ by (prover:"isabelle") }*)
IsaT(X) ==  TRUE (*{ by (prover:"isabelle"; timeout:@) }*)
IsaM(X) ==  TRUE (*{ by (prover:"isabelle"; tactic:@) }*)
IsaMT(X,Y) ==  TRUE (*{ by (prover:"isabelle"; tactic:@; timeout:@) }*)

(***************************************************************************)
(* The following theorem expresses the (useful implication of the) law of  *)
(* set extensionality, which can be written as                             *)
(*                                                                         *)
(*    THEOREM  \A S, T : (S = T) <=> (\A x : (x \in S) <=> (x \in T))      *)
(*                                                                         *)
(* Theorem SetExtensionality is sometimes required by the SMT backend for  *)
(* reasoning about sets. It is usually counterproductive to include        *)
(* theorem SetExtensionality in a BY clause for the Zenon or Isabelle      *)
(* backends. Instead, use the pragma IsaWithSetExtensionality to instruct  *)
(* the Isabelle backend to use the rule of set extensionality.             *)
(***************************************************************************)
IsaWithSetExtensionality == TRUE
           (*{ by (prover:"isabelle"; tactic:"(auto intro: setEqualI)")}*)

THEOREM SetExtensionality == \A S,T : (\A x : x \in S <=> x \in T) => S = T
OBVIOUS

(***************************************************************************)
(* The following theorem is needed to deduce NotInSetS \notin SetS from    *)
(* the definition                                                          *)
(*                                                                         *)
(*   NotInSetS == CHOOSE v : v \notin SetS                                 *)
(***************************************************************************)
THEOREM NoSetContainsEverything == \A S : \E x : x \notin S
OBVIOUS (*{by (isabelle "(auto intro: inIrrefl)")}*)
-----------------------------------------------------------------------------



(********************************************************************)
(********************************************************************)
(********************************************************************)


(********************************************************************)
(* Old versions of Zenon and Isabelle pragmas below                 *)
(* (kept for compatibility)                                         *)
(********************************************************************)


(**************************************************************************)
(* Backend pragma: Zenon with different timeouts (default is 10 seconds)  *)
(*                                                                        *)
(**************************************************************************)

SlowZenon == TRUE (*{ by (prover:"zenon"; timeout:20) }*)
SlowerZenon == TRUE (*{ by (prover:"zenon"; timeout:40) }*)
VerySlowZenon == TRUE (*{ by (prover:"zenon"; timeout:80) }*)
SlowestZenon == TRUE (*{ by (prover:"zenon"; timeout:160) }*)



(********************************************************************)
(* Backend pragma: Isabelle's automatic search ("auto")             *)
(*                                                                  *)
(* This pragma bypasses Zenon. It is useful in situations involving *)
(* essentially simplification and equational reasoning.             *)
(* Default imeout for all isabelle tactics is 30 seconds.           *)
(********************************************************************)
Auto == TRUE (*{ by (prover:"isabelle"; tactic:"auto") }*)
SlowAuto == TRUE (*{ by (prover:"isabelle"; tactic:"auto"; timeout:120) }*)
SlowerAuto == TRUE (*{ by (prover:"isabelle"; tactic:"auto"; timeout:480) }*)
SlowestAuto == TRUE (*{ by (prover:"isabelle"; tactic:"auto"; timeout:960) }*)

(********************************************************************)
(* Backend pragma: Isabelle's "force" tactic                        *)
(*                                                                  *)
(* This pragma bypasses Zenon. It is useful in situations involving *)
(* quantifier reasoning.                                            *)
(********************************************************************)
Force == TRUE (*{ by (prover:"isabelle"; tactic:"force") }*)
SlowForce == TRUE (*{ by (prover:"isabelle"; tactic:"force"; timeout:120) }*)
SlowerForce == TRUE (*{ by (prover:"isabelle"; tactic:"force"; timeout:480) }*)
SlowestForce == TRUE (*{ by (prover:"isabelle"; tactic:"force"; timeout:960) }*)

(***********************************************************************)
(* Backend pragma: Isabelle's "simplification" tactics                 *)
(*                                                                     *)
(* These tactics simplify the goal before running one of the automated *)
(* tactics. They are often necessary for obligations involving record  *)
(* or tuple projections. Use the SimplfyAndSolve tactic unless you're  *)
(* sure you can get away with just Simplification                      *)
(***********************************************************************)
SimplifyAndSolve        == TRUE
    (*{ by (prover:"isabelle"; tactic:"clarsimp auto?") }*)
SlowSimplifyAndSolve    == TRUE
    (*{ by (prover:"isabelle"; tactic:"clarsimp auto?"; timeout:120) }*)
SlowerSimplifyAndSolve  == TRUE
    (*{ by (prover:"isabelle"; tactic:"clarsimp auto?"; timeout:480) }*)
SlowestSimplifyAndSolve == TRUE
    (*{ by (prover:"isabelle"; tactic:"clarsimp auto?"; timeout:960) }*)

Simplification == TRUE (*{ by (prover:"isabelle"; tactic:"clarsimp") }*)
SlowSimplification == TRUE
    (*{ by (prover:"isabelle"; tactic:"clarsimp"; timeout:120) }*)
SlowerSimplification  == TRUE
    (*{ by (prover:"isabelle"; tactic:"clarsimp"; timeout:480) }*)
SlowestSimplification == TRUE
    (*{ by (prover:"isabelle"; tactic:"clarsimp"; timeout:960) }*)

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
Blast == TRUE (*{ by (prover:"isabelle"; tactic:"blast") }*)
SlowBlast == TRUE (*{ by (prover:"isabelle"; tactic:"blast"; timeout:120) }*)
SlowerBlast == TRUE (*{ by (prover:"isabelle"; tactic:"blast"; timeout:480) }*)
SlowestBlast == TRUE (*{ by (prover:"isabelle"; tactic:"blast"; timeout:960) }*)

AutoBlast == TRUE (*{ by (prover:"isabelle"; tactic:"auto, blast") }*)


(**************************************************************************)
(* Backend pragmas: multi-back-ends                                       *)
(*                                                                        *)
(* These pragmas just run a bunch of back-ends one after the other in the *)
(* hope that one will succeed. This saves time and effort for the user at *)
(* the expense of computation time.                                       *)
(**************************************************************************)

(* CVC3 goes first because it's bundled with TLAPS, then the other SMT
   solvers are unlikely to succeed if CVC3 fails, so we run zenon and
   Isabelle before them. *)
AllProvers == TRUE (*{
    by (prover:"cvc33")
    by (prover:"zenon")
    by (prover:"isabelle"; tactic:"auto")
    by (prover:"spass")
    by (prover:"smt3")
    by (prover:"yices3")
    by (prover:"verit")
    by (prover:"z33")
    by (prover:"isabelle"; tactic:"force")
    by (prover:"isabelle"; tactic:"(auto intro: setEqualI)")
    by (prover:"isabelle"; tactic:"clarsimp auto?")
    by (prover:"isabelle"; tactic:"clarsimp")
    by (prover:"isabelle"; tactic:"auto, blast")
  }*)
AllProversT(X) == TRUE (*{
    by (prover:"cvc33"; timeout:@)
    by (prover:"zenon"; timeout:@)
    by (prover:"isabelle"; tactic:"auto"; timeout:@)
    by (prover:"spass"; timeout:@)
    by (prover:"smt3"; timeout:@)
    by (prover:"yices3"; timeout:@)
    by (prover:"verit"; timeout:@)
    by (prover:"z33"; timeout:@)
    by (prover:"isabelle"; tactic:"force"; timeout:@)
    by (prover:"isabelle"; tactic:"(auto intro: setEqualI)"; timeout:@)
    by (prover:"isabelle"; tactic:"clarsimp auto?"; timeout:@)
    by (prover:"isabelle"; tactic:"clarsimp"; timeout:@)
    by (prover:"isabelle"; tactic:"auto, blast"; timeout:@)
  }*)

AllSMT == TRUE (*{
    by (prover:"cvc33")
    by (prover:"smt3")
    by (prover:"yices3")
    by (prover:"verit")
    by (prover:"z33")
  }*)
AllSMTT(X) == TRUE (*{
    by (prover:"cvc33"; timeout:@)
    by (prover:"smt3"; timeout:@)
    by (prover:"yices3"; timeout:@)
    by (prover:"verit"; timeout:@)
    by (prover:"z33"; timeout:@)
  }*)

AllIsa == TRUE (*{
    by (prover:"isabelle"; tactic:"auto")
    by (prover:"isabelle"; tactic:"force")
    by (prover:"isabelle"; tactic:"(auto intro: setEqualI)")
    by (prover:"isabelle"; tactic:"clarsimp auto?")
    by (prover:"isabelle"; tactic:"clarsimp")
    by (prover:"isabelle"; tactic:"auto, blast")
  }*)
AllIsaT(X) == TRUE (*{
    by (prover:"isabelle"; tactic:"auto"; timeout:@)
    by (prover:"isabelle"; tactic:"force"; timeout:@)
    by (prover:"isabelle"; tactic:"(auto intro: setEqualI)"; timeout:@)
    by (prover:"isabelle"; tactic:"clarsimp auto?"; timeout:@)
    by (prover:"isabelle"; tactic:"clarsimp"; timeout:@)
    by (prover:"isabelle"; tactic:"auto, blast"; timeout:@)
  }*)

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
                   PROVE  [][N]_f /\ WF_f(A) /\ []F => []<><<M>>_g \/ []<>(~EM)

THEOREM RuleSF2 == ASSUME STATE P, STATE f, STATE g, STATE EM,
                          ACTION A, ACTION B, ACTION N, ACTION M,
                          TEMPORAL F,
                          <<N /\ B>>_f => <<M>>_g,
                          P /\ P' /\ <<N /\ A>>_f /\ EM => B,
                          P /\ EM => ENABLED A,
                          [][N /\ ~B]_f /\ SF_f(A) /\ []F /\ []<>EM => <>[]P
                   PROVE  [][N]_f /\ SF_f(A) /\ []F => []<><<M>>_g \/ <>[](~EM)


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
PropositionalTemporalLogic == TRUE
=============================================================================
