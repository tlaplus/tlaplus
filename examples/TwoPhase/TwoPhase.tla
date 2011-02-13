---------------------- MODULE TwoPhase -----------------------
(***************************************************************************)
(* This module specifies the two-phase handshake, which is a simple but    *)
(* very important hardware protocol by which a Producer process and a      *)
(* Consumer process alternately perform actions, with the Producer going   *)
(* first.  The system is pictured as follows:                              *)
(*                                                                         *)
(* `.                                                                      *)
(*     ------------           p          ------------                      *)
(*    |            | -----------------> |            |                     *)
(*    |  Producer  |                    |  Consumer  |                     *)
(*    |            | <----------------- |            |                     *)
(*     ------------           c          ------------    .'                *)
(*                                                                         *)
(*                                                                         *)
(* In the spec, we represent the Producer and Consumer actions the way we  *)
(* represented the actions A_0 and A_1 of the Alternate specification.  We *)
(* then show that this specification implements the Alternate              *)
(* specification under a suitable refinement mapping (substitution for the *)
(* variable v).                                                            *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

CONSTANT XInit(_), XAct(_, _, _)
 
VARIABLE p, c, x

Init == /\ p = 0 
        /\ c = 0
        /\ XInit(x)

ProducerStep == /\ p = c
                /\ XAct(0, x, x')
                /\ p' = (p + 1) % 2
                /\ c' = c

ConsumerStep == /\ p # c
                /\ XAct(1, x, x')
                /\ c' = (c + 1) % 2
                /\ p' = p

Next == ProducerStep \/ ConsumerStep

Spec == Init /\ [][Next]_<<p, c, x>>


(***************************************************************************)
(* Inv is the invariant that is needed for the proof.                      *)
(***************************************************************************)
Inv == (p \in {0,1}) /\ (c \in {0,1})

(***************************************************************************)
(* We prove that specification Spec implement (implies) the specification  *)
(* obtained by substiting a state function vBar for the variable v, where  *)
(* vBar is defined as follows.                                             *)
(***************************************************************************)
vBar == (p + c) % 2

(***************************************************************************)
(* The following statement imports, for every defined operator D of module *)
(* Alternate, a definition of A!D to equal the definition of D with vBar   *)
(* substituted for v and with the parameters x, XInit, and XAct of this    *)
(* module substituted for the parameters of the same name of module        *)
(* Alternate.  Thus, A!Spec is defined to be the formula Spec of module    *)
(* Alternate with vBar substituted for v.                                  *)
(***************************************************************************)
A == INSTANCE Alternate WITH v <- vBar

(***************************************************************************)
(* Our proof requires the following simple fact about the modulus operator *)
(* % .  It is proved using a decision procedure, as explained in the       *)
(* comments in the TLAProofRules module.                                   *)
(*                                                                         *)
(* Often, a proof requires a simple mathematical fact that cannot be       *)
(* deduced so easily by the Proof System.  In fact, the Proof System may   *)
(* not even know some basic mathematical facts needed to prove it.         *)
(* Proving the needed fact is a fun exercise for those who enjoy that sort *)
(* of thing.  It's painful for the rest of us.  Eventually, we will have a *)
(* library with lots of useful facts that you can import.  But such a      *)
(* library is unlikely ever to contain all the simple mathematical         *)
(* theoresm that you'll ever need.                                         *)
(*                                                                         *)
(* We are primarily interested in making the Proof System useful to people *)
(* who want to prove things about algorithms and systems, not for those    *)
(* who want to prove theorems of mathematics.  (We hope that the Proof     *)
(* System will be good for doing those proofs too, but we are not doing    *)
(* anything special to achieve this.)  We expect that most users will      *)
(* simply assume these mathematical facts.  However, it's dangerous to     *)
(* assume the truth of a theorem without checking it in some way.  It's    *)
(* easy to make a mistake and write a false theorem, and assuming a false  *)
(* theorem could allow you to prove other false theorems.  So, you should  *)
(* use the TLC model checker to check any fact that you assume.  In most   *)
(* cases, TLC won't be able to check the actual theorem.  But it should be *)
(* able to do a good enough job to catch errors.  For example, TLC can't   *)
(* check that a theorem is true for all integers.  However, in practice we *)
(* expect that you will be able to check it for a large enough subset of   *)
(* the integers to gain sufficient confidence that the theorem really is   *)
(* true.  In this case, TLC could check the actual theorem.                *)
(***************************************************************************)
THEOREM Mod2 == \A i \in {0,1} : /\ (i + 1) % 2 = 1 - i
                                 /\ (i + 0) % 2 = i
BY SimpleArithmetic


(***************************************************************************)
(* The following theorem is a standard proof that one specification        *)
(* implements (the safety part of) another specification under a           *)
(* refinement mapping.  In fact, the temporal leaf proofs will be exactly  *)
(* the same one-liners for every such proof.  In realistic example, the    *)
(* non-temporal leaf proofs will be replaced by fairly long structured     *)
(* proofs--especially the two substeps numbered <2>2.                      *)
(***************************************************************************)
THEOREM Implementation == Spec => A!Spec
<1>1. Spec => []Inv
  <2>1. Init => Inv
    BY DEF Init, Inv
  <2>2. Inv /\ [Next]_<<p, c, x>> => Inv'
    BY Mod2 DEF Inv, Next, ProducerStep, ConsumerStep
  <2>3. QED
\*    <3>1. Inv /\ [][Next]_<<p, c, x>> => []Inv
\*       BY <2>2, Inv1 
\*    <3>2. QED
\*       BY <3>1, <2>1 DEF Spec
   PROOF OMITTED  \* TLAPS does not yet do temporal-logic reasoning
<1>2. QED
  <2>1. Init => A!Init
    BY Mod2 DEF Init, A!Init, vBar
  <2>2. Inv /\ [Next]_<<p, c, x>>  => [A!Next]_<<vBar, x>>
    BY Mod2 DEF Inv, Next, ProducerStep, ConsumerStep, A!Next, vBar
  <2>3. []Inv /\ [][Next]_<<p, c, x>>  => [][A!Next]_<<vBar, x>>  
\*     BY <2>2, StepSimulation
     PROOF OMITTED  \* TLAPS does not yet do temporal-logic reasoning
  <2>4. QED
\*     BY <2>1, <2>3, <1>1 DEF Spec, A!Spec
     PROOF OMITTED  \* TLAPS does not yet do temporal-logic reasoning
  
==============================================================
\* Generated at Sat Oct 31 03:15:55 PDT 2009
