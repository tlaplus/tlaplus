------------------------------- MODULE TLCExt -------------------------------

LOCAL INSTANCE TLC
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

-----------------------------------------------------------------------------

\* AssertEq(a, b) is logically equivalent to the expression 'a = b'. If a and b are not equal, 
\* however, AssertEq(a, b) will print out the values of 'a' and 'b'. If the two values are equal,
\* nothing will be printed.
AssertEq(a, b) == 
    IF a # b THEN
        /\ PrintT("Assertion failed")
        /\ PrintT(a)
        /\ PrintT(b)
        /\ a = b
    ELSE a = b


AssertError(err, exp) ==
    LET FailsEval(e) == CHOOSE b \in BOOLEAN : TRUE \* Expression failed to evaluate. 
        TLCError     == CHOOSE s \in STRING  : TRUE \* TLC error string.
    IN IF FailsEval(exp) THEN Assert(err = TLCError, TLCError) ELSE TRUE

-----------------------------------------------------------------------------

Trace == 
  (******************************************************************************)
  (* The sequence of states (represented as a record whose DOMAIN is the set of *)
  (* a spec's variables) from an initial state to the current state.  In other  *)
  (* words, a prefix - of a behavior - ending with the current state.  A way to *)
  (* think about this operator is to see it as an implicit history variable     *)
  (* that does not have to be explicitly specified at the level of the spec.    *)
  (*                                                                            *)
  (* Note that op is incompatible with TLC!RandomElement and Randomization (see *)
  (* tlc2.tool.TLCTrace.getTrace(LongVec)) and will cause TLC to crash.  This   *)
  (* technical limitation could be removed though.                              *)
  (*                                                                            *)
  (* Beware that Trace is prohibitively expensive when evaluated as part of     *)
  (* the next-state relation or constraints in model-checking mode.             *)
  (******************************************************************************)
  TRUE \* TODO

-----------------------------------------------------------------------------

(* HERE BE DRAGONS! The operators below are experimental! *)

CounterExample ==
    (****************************************************************************)
    (* In the scope of POSTCONDITION, the operator CounterExample is equivalent *)
    (* to a (directed) graph represented as [state: States, action: Actions]    *)
    (* with                                                                     *)
    (*   States \subseteq [ Variables -> Values ]                               *)
    (* and                                                                      *)
    (*  Actions \subseteq                                                       *)
    (*            (CounterExample.state \X Action \X CounterExample.state).     *)
    (* If TLC found no violations, then CounterExample.states equals {} and     *)
    (* CounterExample.actions equals {}.  If only initial state violates a      *)
    (* (safety) property, CounterExample.state is a set of those states, and    *)
    (* CounterExample.actions = {}.                                             *)
    (****************************************************************************)
    TRUE

ToTrace(CE) ==
	TRUE

-----------------------------------------------------------------------------

TLCModelValue(str) ==
  (******************************************************************************)
  (* A model value is an unspecified value that TLC considers to be unequal to  *)
  (* any value that you can express in TLA+.                                    *)
  (*                                                                            *)
  (* In most cases, TLC model values can and should be declared via the TLC     *)
  (* config file.  However, for large sets of model values, it can become       *)
  (* tedious to enumerate them explicitly. Large sets of model values usually   *)
  (* appear when simulating TLA+ specs with TLC. The following example defines  *)
  (* a set of 32 model values:                                                  *)
  (*                                                                            *)
  (*  SetOfModelValues == {TLCModelValue("T_MV" \o ToString(i)) : i \in 1..32}  *)
  (*                                                                            *)
  (* As a matter of fact, the example defines a set of "typed" model values:    *)
  (* TLC considers a typed model value to be unequal to any other model value   *)
  (* of the same type.  However, it produces an error when evaluating an        *)
  (* expression requires it to determine if a typed model value is equal to any *)
  (* value other than a model value of the same type or an ordinary model       *)
  (* value.                                                                     *)
  (*                                                                            *)
  (* A model-value type consists of a single letter, so there are 52 different  *)
  (* types because  a  and  A  are different types.  (TLC actually accepts      *)
  (* digits and underscore as types; don't use them.)  A model value has type   *)
  (* T  if and only if its name begins with the two characters  T_ .            *)
  (*                                                                            *)
  (* TLCModelValue may only appear in constant definitions!  Expect bogus       *)
  (* behavior if TLCModelValue appears in the behavior spec, constraints,       *)
  (* invariants, or properties.                                                 *)
  (******************************************************************************)
  CHOOSE v: ToString(v) = str

TLCDefer(expression) ==
  (******************************************************************************)
  (* Defer evaluation of expression to some later time or never.                *)
  (*                                                                            *)
  (* For TLC's simulation mode, later is defined as the point of time when      *)
  (* simulation has chosen a successor state to extend the prefix of the        *)
  (* current behavior.                                                          *)
  (*                                                                            *)
  (* A use case is TLCDefer(TLCSet(42, someVal)), which sets someVal only       *)
  (* for the states of the behavior and not the set of all successor states     *)
  (* of all states in the behavior.                                             *)
  (******************************************************************************)
  TRUE

-----------------------------------------------------------------------------

TLCNoOp(val) ==
  (******************************************************************************)
  (* No-operation operator (does nothing).  Only useful to debug TLC's          *)
  (* evaluator that is written in Java: Insert TLCNoOp into the expression      *)
  (* whose evaluation you wish to debug and set a breakpoint in this            *)
  (* operator's Java module override TLCExt#tlcNoOp in TLCExt.java.             *)
  (******************************************************************************)
  val


PickSuccessor(exp) ==
  (******************************************************************************)
  (* When set as an action constraint in the configuration file, interactively  *)
  (* pick successor states during state exploration, iff the expression exp     *)
  (* evaluates to FALSE.  To always pick successor states manually, use         *)
  (* PickSuccessor(FALSE). To pick successor states when the current prefix of  *)
  (* behaviors exceeds 22 states, use PickSuccessor(TLCGet("level") < 23).      *)
  (* Evaluates to TRUE when evaluated in the context of a constant- or          *)
  (* state-level formula.  Also evaluates to TRUE if PickSuccessor appears as   *)
  (* part of the next-state relation and the successor state has not been       *)
  (* fully determined yet.                                                      *)
  (******************************************************************************)
  IF (exp)
  THEN TRUE
  ELSE CHOOSE bool \in BOOLEAN : TRUE 

-----------------------------------------------------------------------------

TLCCache(expression, closure) ==
  (******************************************************************************)
  (* Equals the value that an earlier evaluation of the expression evaluated to *)
  (* iff the closure of the earlier evaluation and this evaluation are equal.   *)
  (*                                                                            *)
  (* Currently only implemented for state-level formulas.  See TLC!TLCEval for  *)
  (* constant-level formulas.                                                   *)
  (******************************************************************************)
  expression

============================================================================
