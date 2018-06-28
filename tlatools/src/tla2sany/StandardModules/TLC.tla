------------------------------- MODULE TLC ----------------------------------
(***************************************************************************)
(* This is a standard module for use with the TLC model checker.           *)
(* Operators not explained by comments here are explained in the book      *)
(* "Specifying Systems".                                                   *)
(*                                                                         *)
(* The definitions of all the operators in this module are overridden by   *)
(* TLC with methods defined in the Java class tlc2.module.TLC.  Each       *)
(* definition is overridden with the method of the same name, except that  *)
(* the mapping from infix operators to Java methods is specified in the    *)
(* static block at the beginning of the Java class.                        *)
(***************************************************************************)
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
-----------------------------------------------------------------------------
Print(out, val) == val
PrintT(out) == TRUE
   (************************************************************************)
   (* This expression equals TRUE, but evaluating it causes TLC to print   *)
   (* the value of out.                                                    *)
   (************************************************************************)
   
Assert(val, out) == IF val = TRUE THEN TRUE
                                  ELSE CHOOSE v : TRUE
JavaTime == CHOOSE n : n \in Nat

(***************************************************************************)
(* TLC can read and set a special list of values while evaluating          *)
(* expressions using the operators TLCSet and TLCGet.  When TLC evaluates  *)
(* TLCSet(i,v), for any positive integer i and arbitrary value v, it       *)
(* obtains the value TRUE and sets element number i of the list to v.      *)
(* When TLC evaluates TLCGet(i), the value it obtains is the current value *)
(* of the element number i of this list.                                   *)
(*                                                                         *)
(* One use of this feature is to check TLC's progress during long          *)
(* computations.  For example, suppose TLC is evaluating a formula         *)
(* \A x \in S : P where S is a large set, so it evaluates P many times.    *)
(* You can use TLCGet, TLCSet, and Print to print something after every    *)
(* 1000 times TLC evaluates P.                                             *)
(*                                                                         *)
(* As explained in the description of the TLCEval operator below, you may  *)
(* also want to use this feature to count how many times TLC is evaluating *)
(* an expression e.  To use value number i as the counter, just replace e  *)
(* by                                                                      *)
(*                                                                         *)
(*   IF TLCSet(i, TLCGet(i)+1) THEN e ELSE 42                              *)
(*                                                                         *)
(* (The ELSE expression is never evaluated.)                               *)
(*                                                                         *)
(* For reasons of efficiency, TLCGet and TLCSet behave somewhat strangely  *)
(* when TLC is run with multiple worker threads.  Each worker thread       *)
(* maintains its own individual copy of the list of values on which it     *)
(* evaluates TLCGet and TLCSet.  The worker threads are activated only     *)
(* after the computation and invariance checking of the initial states.    *)
(* Before then, evaluating TLCSet(i,v) sets the element i of the list      *)
(* maintained by all threads.  Thus, the lists of all the worker threads   *)
(* can be initialized by putting the appropriate TLCSet expression in an   *)
(* ASSUME expression or in the initial predicate.                          *)
(***************************************************************************)
TLCGet(i) == CHOOSE n : TRUE
TLCSet(i, v) == TRUE
-----------------------------------------------------------------------------
d :> e == [x \in {d} |-> e]
f @@ g == [x \in (DOMAIN f) \cup (DOMAIN g) |->
            IF x \in DOMAIN f THEN f[x] ELSE g[x]]
Permutations(S) == 
   {f \in [S -> S] : \A w \in S : \E v \in S : f[v]=w}
-----------------------------------------------------------------------------
(***************************************************************************)
(* In the following definition, we use Op as the formal parameter rather   *)
(* than \prec because TLC Version 1 can't handle infix formal parameters.  *)
(***************************************************************************)
SortSeq(s, Op(_, _)) ==
    LET Perm == CHOOSE p \in Permutations(1 .. Len(s)) :
                  \A i, j \in 1..Len(s) : 
                     (i < j) => Op(s[p[i]], s[p[j]]) \/ (s[p[i]] = s[p[j]])
    IN  [i \in 1..Len(s) |-> s[Perm[i]]]

(***************************************************************************)
(* TLC evaluates RandomElement(S) to be a pseudo-randomly chosen element   *)
(* of the set S, where each element of S is chosen with equal probability. *)
(* This feature was added to enable the computation of statistical         *)
(* properties of a specification's executions by running TLC in simulation *)
(* mode.  We don't know if anyone has ever done this.                      *)
(*                                                                         *)
(* In breadth-first search model checking, the pseudo-random choices made  *)
(* when computing possible steps satisfying the next-state relation are    *)
(* determined by the first state of the step.  Thus, the choices made for  *)
(* a particular state will be the same in successive runs of TLC.  This is *)
(* done to permit TLC to generate an error trace if an error is found.     *)
(* This applies only when TLC is run in breadth-first search mode.  The    *)
(* random choices made in simulation mode are independent of the state for *)
(* which they are made.                                                    *)
(***************************************************************************)
RandomElement(s) == CHOOSE x \in s : TRUE

(***************************************************************************)
(* The constant value Any has the special property that, for any value v,  *)
(* TLC evaluates the expression  v \in Any  to equal TRUE.  The special    *)
(* value Any was introduced because TLA+ originally allowed only functions *)
(* to be defined recursively, and it was sometimes convenient to define a  *)
(* function with domain Any.  It is retained for backwards compatibility.  *)
(***************************************************************************)
Any == CHOOSE x : TRUE

ToString(v) == (CHOOSE x \in [a : v, b : STRING] : TRUE).b
   (************************************************************************)
   (* This equals a string that is the TLA+ representation of the value    *)
   (* that TLC obtains by evaluating v.                                    *)
   (************************************************************************)

(***************************************************************************)
(* TLC often uses lazy evaluation.  For example, it may not enumerate the  *)
(* elements of a set of the form {x \in T : P(x)} unless it has to; and it *)
(* doesn't have to if it only needs to check if an element e is in that    *)
(* set.  (TLC can do that by evaluating x \in T and P(e).) TLC uses        *)
(* heuristics to determine when it should completely evaluate an           *)
(* expression.  Those heuristics work well most of the time.  However,     *)
(* sometimes lazy evaluation can result in the expression ultimately being *)
(* evaluated multiple times instead of just once.  This can especially be  *)
(* a problem when evaluating a recursively defined operator.  You can get  *)
(* TLC to fully evaluate an expression exp and not use lazy evaluation by  *)
(* replacing exp with TLCEval(exp).                                        *)
(*                                                                         *)
(* If TLC is taking a long time to evaluate something, you can check if    *)
(* lazy evaluation is the source of the problem by using the TLCSet and    *)
(* TLCGet operators to count how many times expressions are being          *)
(* evaluated.                                                              *)
(***************************************************************************)
TLCEval(v) == v

=============================================================================