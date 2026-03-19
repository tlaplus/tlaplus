----------------------------- MODULE Stuttering ----------------------------
(***************************************************************************)
(* This module is explained in Section 5 of the paper "Auxiliary Variables *)
(* in TLA+".  It defines operators used to add a stuttering variable s to  *)
(* a specification `Spec' to form a specification SpecS.  It is mean to be *)
(* instantiated with s replaced by the stuttering variable to be added and *)
(* vars replaced by the tuple of all variables in the original             *)
(* specification.                                                          *)
(*                                                                         *)
(* If Init is the initial predicate of `Spec', then the initial predicate  *)
(* of SpecS is Init /\ (s = top) , where top is defined below.             *)
(*                                                                         *)
(* The next-state action of SpecS is obtained by replacing each subaction  *)
(* `A' of a disjunctive representation of the next-state action Next of    *)
(* `Spec' with an action `AS' written in terms of operators defined below. *)
(* (Disjunctive representations are described in Section 3.2 of "Auxiliary *)
(* Variables in TLA+".) Action `AS' executes `A' and stuttering steps      *)
(* added either before or after an `A' step.  The basic idea is that s     *)
(* equals top except while stuttering steps are being taken, when it is a  *)
(* record with the following fields:                                       *)
(*                                                                         *)
(*   id: A value that identifies the action `A'.                           *)
(*                                                                         *)
(*   ctxt: A value identifying the context under which `A' is executed.    *)
(*         For example, if `A' appears in a formula `\E i, j \in S : A' ,  *)
(*         this would equal the value of the pair <<i, j>> for             *)
(*         which `A' is being executed.                                    *)
(*                                                                         *)
(*   val: A value that is decremented by each stuttering step, until       *)
(*        it reaches a minimum value.                                      *)
(*                                                                         *)
(* The arguments of the operators defined in this module have the          *)
(* following meanings.                                                     *)
(*                                                                         *)
(* `A'                                                                     *)
(*   The subaction `A' of Next.                                            *)
(*                                                                         *)
(* id                                                                      *)
(*   A string identifying action `A'.                                      *)
(*                                                                         *)
(* `Sigma'                                                                 *)
(*   A set of values ordered by some "less-than" relation.  This is        *)
(*   the set of possible values of s.val when executing stuttering         *)
(*   steps before or after subaction `A'.                                  *)
(*                                                                         *)
(* bot                                                                     *)
(*   The minimum element of Sigma under its less-than relation.            *)
(*                                                                         *)
(* initVal                                                                 *)
(*   The initial value to which s.val is set for executing stuttering      *)
(*   steps before or after `A'.                                            *)
(*                                                                         *)
(* decr                                                                    *)
(*   An operator such that each stuttering step changes s.val to           *)
(*   decr(s.val).                                                          *)
(*                                                                         *)
(* `context'                                                               *)
(*   The context in which `A' appears.  It is the expression that is       *)
(*   evaluated to determine the value to which s.ctxt is set.              *)
(*                                                                         *)
(* `enabled'                                                               *)
(*   A formula equivalent to `ENABLED A'.  You can always take it to be    *)
(*   `ENABLED A', but you can usually find an expression that equals       *)
(*   `ENABLED A' in every reachable state of `Spec' but is easier for      *)
(*   TLC to compute.                                                       *)
(***************************************************************************)
EXTENDS Naturals, TLC
top == [top |-> "top"] 

VARIABLES s, vars

(***************************************************************************)
(* Equals `AS' when no stuttering steps are being added before or after    *)
(* `A'.                                                                    *)
(***************************************************************************)
NoStutter(A) == (s = top) /\ A /\ (s' = s)

(***************************************************************************)
(* The PostStutter and PreStutter operators define actions that perform    *)
(* stuttering steps after xecuting `A' and before executing `A',           *)
(* respectively.  If bot = 1, initVal = 42, and decr(i) = i-1, then the    *)
(* actions they define add 42 stuttering steps.  They always add at least  *)
(* one stuttering step.                                                    *)
(***************************************************************************)
PostStutter(A, actionId, context, bot, initVal, decr(_)) ==
  IF s = top THEN /\ A 
                  /\ s' = [id |-> actionId, ctxt |-> context, val |-> initVal]
             ELSE /\ s.id = actionId
                  /\ s.ctxt = context \* MODIFIED HERE
                  /\ UNCHANGED vars 
                  /\ s'= IF s.val = bot THEN top 
                                        ELSE [s EXCEPT !.val = decr(s.val)]

PreStutter(A, enabled, actionId, context, bot, initVal, decr(_)) == 
  IF s = top 
    THEN /\ enabled
         /\ UNCHANGED vars 
         /\ s' = [id |-> actionId, ctxt |-> context, val |-> initVal] 
    ELSE /\ s.id = actionId
         /\ s.ctxt = context \* MODIFIED HERE
         /\ IF s.val = bot THEN /\ s.ctxt = context
                                /\ A 
                                /\ s' = top
                           ELSE /\ UNCHANGED vars  
                                /\ s' = [s EXCEPT !.val = decr(s.val)]

(***************************************************************************)
(* The operators MayPostStutter and MayPreStutter are like PostStutter and *)
(* PreStutter, except they add one fewer stuttering step.  For example, if *)
(* bot = 1, initVal = 42, and decr(i) = i-1, then they add 42 steps.  If   *)
(* initVal = bot, then they simply execute A without any added stuttering  *)
(* steps.                                                                  *)
(***************************************************************************)                                 
MayPostStutter(A, actionId, context, bot, initVal, decr(_)) ==
  IF s = top THEN /\ A 
                  /\ s' = IF initVal = bot
                            THEN s
                            ELSE [id |-> actionId, ctxt |-> context, 
                                  val |-> initVal]
             ELSE /\ s.id = actionId
                  /\ s.ctxt = context \* MODIFIED HERE
                  /\ UNCHANGED vars 
                  /\ s'= IF decr(s.val) = bot 
                           THEN top 
                           ELSE [s EXCEPT !.val = decr(s.val)]

MayPreStutter(A, enabled, actionId, context, bot, initVal, decr(_)) == 
  IF s = top 
    THEN /\ enabled
         /\ IF initVal = bot
              THEN A /\ (s' = s)
              ELSE /\ s' = [id |-> actionId, ctxt |-> context, val |-> initVal]
                   /\ UNCHANGED vars         
    ELSE /\ s.id = actionId
         /\ s.ctxt = context \* MODIFIED HERE 
         /\ IF s.val = bot THEN /\ s.ctxt = context
                                /\ A 
                                /\ s' = top
                           ELSE /\ UNCHANGED vars  
                                /\ s' = [s EXCEPT !.val = decr(s.val)] 
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following operator is true iff repeatedly apply decr to any element *)
(* sig of Sigma produces a sequence sig, decr(sig), decr(decr(sig)), ...   *)
(* that eventually arrives at bot.  This condition should be satisfied by  *)
(* the values of Sigma, bot, and decr used with the operators defined      *)
(* above to add stuttering steps to an action.                             *)
(***************************************************************************)
StutterConstantCondition(Sigma, bot, decr(_)) ==
  LET InverseDecr(S) == {sig \in Sigma \ S : decr(sig) \in S}
      R[n \in Nat] == IF n = 0 THEN {bot}
                               ELSE LET T == R[n-1] 
                                    IN  T \cup InverseDecr(T)
                        
  IN Sigma = UNION {R[n] : n \in Nat}

(***************************************************************************)
(* TLC can evaluate StutterConstantCondition only in a model that replaces *)
(* Nat by the set 0..n for some integer n.  The following operator is      *)
(* equivalent to StutterConstantCondition when Sigma is a finite set, but  *)
(* doesn't require modifying any definitions.                              *)
(***************************************************************************)
AltStutterConstantCondition(Sigma, bot, decr(_)) ==
   LET InverseDecr(S) == {sig \in Sigma \ S : decr(sig) \in S}
       ReachBot[S \in SUBSET Sigma] ==
          IF InverseDecr(S) = {} THEN S 
                                 ELSE ReachBot[S \cup InverseDecr(S)]
   IN  ReachBot[{bot}] = Sigma
=============================================================================
\* Modification History
\* Last modified Sat Dec 31 17:47:02 PST 2016 by lamport
\* Created Tue Dec 08 11:51:34 PST 2015 by lamport

(*****************************************************************************)
(* This module comes from :                                                  *)
(* L. Lamport and S. Merz, "Auxiliary variables in TLA+",                    *)
(*   arXiv preprint arXiv:1703.05121, 2017.                                  *)
(*                                                                           *)
(* It has been modified slightly to ensure correctness whenever actions are  *)
(* are taken during a stuttering step (e.g. modifying a history variable)    *)
(* Search for the lines containing "MODIFIED HERE".                          *)
(* Indeed, the context variable is not always verified whenever a stutter    *)
(* step is taken.                                                            *)
(* Using specifications created from PlusCal and wanting to add stuttering   *)
(* to a certain transition, one might to put the label as an actionId and    *)
(* the process identifier as a context. Without modifications, and in the    *)
(* previously mentioned context, the stuttering does not behave correctly,   *)
(* as another process could advance the stuttering and possibly break the    *)
(* updating of variables.                                                    *)
(* Another solution could be to set the actionId to the <<label, procId>>    *)
(* tuple. (this has not been verified)                                       *)
(*****************************************************************************)