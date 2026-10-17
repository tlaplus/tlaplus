-------------------- MODULE Github1445 --------------------
EXTENDS Integers, TLC
VARIABLES x, y

\* Enumerated in unsorted order, and lazy because neither side of \cup is an
\* interval or an enumerated set.
D == {s \in SUBSET (12..22) : s # {}} \cup SUBSET (1..11)

\* 8 initial states, so that all workers evaluate the actions concurrently.
Init == x = 0 /\ y \in 1..8

\* One successor per element of S and initial state.  The k-th Enum action
\* maps y to -(8 * k + 1)..-(8 * k + 8).
Enum(S, k) == y > 0 /\ x' \in S /\ y' = -(y + 8 * k)

\* A single successor, shared by all initial states.
Assign(S) == y > 0 /\ x' = S /\ y' = 0

Next ==
    \* Set bound by \E that becomes part of a state, which workers fingerprint.
    \* The outer set has a single element, so the inner set remains
    \* unnormalized.  This disjunct comes first, so that all workers fingerprint
    \* the set at the same time instead of one after the other.
    \/ \E T \in {{6145 - i : i \in 1..2048}} : Assign(T)
    \* Constant-level argument with a flat set in descending order.
    \/ Enum({2049 - i : i \in 1..2048}, 0)
    \* Constant-level argument with a set of tuples in descending order.
    \/ Enum({<<2049 - i>> : i \in 1..2048}, 1)
    \* Set bound by \E. The outer set has a single element, so the inner set
    \* remains unnormalized.
    \/ \E T \in {{4097 - i : i \in 1..2048}} : Enum(T, 2)
    \* Lazy set (SetPredValue) that becomes part of a state.
    \/ Assign({s \in D : TRUE})
    \* Lazy function (FcnLambdaValue) that becomes part of a state.
    \/ Assign([s \in D |-> s])
    \* Workers evaluate the liveness tableau only for states they expand.
    \/ y <= 0 /\ UNCHANGED <<x, y>>

vars == <<x, y>>

\* A step of Enum(..., 0) that is enabled iff S contains 1024.  Liveness checking
\* evaluates Take(S) for all steps, so y' = -y excludes the other actions before
\* x' is compared to an integer.
Take(S) == y > 0 /\ y' = -y /\ x' = 1024 /\ 1024 \in {e \in S : TRUE}

\* Liveness#astToLive binds S in the contexts of ENABLED Take(S) and Take(S).
\* The subscript is y, because x cannot be compared across actions.
Spec == /\ Init /\ [][Next]_vars
        /\ \A S \in {{2049 - i : i \in 1..2048}} : WF_y(Take(S))

\* SpecProcessor unrolls the \A of a property, which binds S in the context of
\* an invariant.
Inv == \A S \in {{2049 - i : i \in 1..2048}} :
            [](y \in -8..-1 => \E e \in S : e = x)

\* Same as Inv but for a liveness property.  The set constructor defers the
\* enumeration of S to state exploration, because Liveness#astToLive expands
\* \E e \in S : ... when it constructs the tableau.
Live == \A S \in {{2049 - i : i \in 1..2048}} :
            <>[](y \in -8..-1 => x \in {e \in S : TRUE})

\* Weak fairness of Take rules out stuttering in an initial state forever.
Fair == <>(y <= 0)

-----------------------------------------------------------

\* The specs below have no action arguments, so that Tool#getActions binds no
\* values and only the property under test races.  The sets are literals,
\* because naming them in a constant definition hides the race.

\* 8 * 2048 successor states, each of which stutters.
NextStutter == \/ y > 0 /\ x' \in 1..2048 /\ y' = -y
               \/ y < 0 /\ UNCHANGED vars

SpecStutter == Init /\ [][NextStutter]_vars

\* Same as NextStutter, but returns to an initial state, so that the steps of
\* the first disjunct recur.
NextCycle == \/ y > 0 /\ x' \in 1..2048 /\ y' = -y
             \/ y < 0 /\ x' = 0 /\ y' = -y

SpecCycle == Init /\ [][NextCycle]_vars /\ WF_vars(NextCycle)

\* SpecProcessor unrolls the \A of a property, which binds S in the context of
\* an implied action.
ImpliedAction == \A S \in {{2049 - i : i \in 1..2048}} :
                    [][y > 0 => \E e \in S : e = x']_vars

\* Liveness#astToLive binds S in the context of an action (LNAction) of the
\* tableau.
ActionLive == \A S \in {{2049 - i : i \in 1..2048}} :
                    []<><<y > 0 /\ \E e \in S : e = x'>>_vars

\* Same as Live but for \E, which Liveness#astToLive binds in the context of a
\* state predicate (LNStateAST) of the tableau.
ExistsLive == \E S \in {{2049 - i : i \in 1..2048}} :
                    <>[](x = 0 \/ x \in {e \in S : TRUE})

-----------------------------------------------------------

\* SpecProcessor unrolls the \A of each property below, which binds a lazy
\* set or function P in the context of an invariant.  The first comparison of
\* P with another value enumerates P and caches the result in P, and workers
\* race to normalize the cache.  The \X keeps the operands of \cup lazy, and
\* puts the elements of the cache out of order.

\* The cache of SetPredValue.
PredCache == \A P \in {{t \in ((1025..2048) \X {0}) \cup ((1..1024) \X {0}) : TRUE}} :
                [](y < 0 => P # {} /\ \E e \in P : e = <<x, 0>>)

\* The cache of SetCupValue.
CupCache == \A P \in {((1025..2048) \X {0}) \cup ((1..1024) \X {0})} :
                [](y < 0 => P # {} /\ \E e \in P : e = <<x, 0>>)

\* The cache of SetCapValue.
CapCache == \A P \in {(((1025..2048) \X {0}) \cup ((1..1024) \X {0})) \cap ((1..2048) \X {0})} :
                [](y < 0 => P # {} /\ \E e \in P : e = <<x, 0>>)

\* The cache of SetDiffValue.
DiffCache == \A P \in {(((1025..2048) \X {0}) \cup ((1..1024) \X {0})) \ {<<0, 0>>}} :
                [](y < 0 => P # {} /\ \E e \in P : e = <<x, 0>>)

\* The cache of UnionValue.  The sets overlap, so that the cache has
\* duplicates and is out of order.
UnionCache == \A P \in {UNION {1..2048, 2..2048}} :
                [](y < 0 => P # {} /\ \E e \in P : e = x)

\* The cache of SetOfTuplesValue.
TuplesCache == \A P \in {(UNION {1..2048, 2..2048}) \X {0}} :
                [](y < 0 => P # {} /\ \E e \in P : e = <<x, 0>>)

\* The cache of SetOfFcnsValue.
FcnsCache == \A P \in {[{0} -> UNION {1..2048, 2..2048}]} :
                [](y < 0 => P # {} /\ \E f \in P : f[0] = x)

\* The cache of SetOfRcdsValue.
RcdsCache == \A P \in {[a : UNION {1..2048, 2..2048}]} :
                [](y < 0 => P # {} /\ \E r \in P : r.a = x)

\* The cache of FcnLambdaValue.
LambdaCache == \A P \in {[t \in ((1025..2048) \X {0}) \cup ((1..1024) \X {0}) |-> t[1]]} :
                [](y < 0 => P = P /\ P[<<x, 0>>] = x)

-----------------------------------------------------------

\* SpecProcessor unrolls the \A of each property below, which binds a lazy set
\* or function P in the context of an invariant.  Publishing P cannot
\* normalize it, because its domain Nat is infinite.  P evaluates its body in
\* the context of the LET, which binds K to a LazyValue, and in the empty state
\* in which TLC created P.  Thus, the value of K that the first worker caches
\* in the LazyValue applies to all workers.  Workers race to normalize the
\* cached value, a set in descending order, when they enumerate it.

\* Lazy set (SetPredValue).
LazyPred == \A P \in {LET K == {2049 - i : i \in 1..2048}
                      IN {n \in Nat : \E e \in K : e = n}} :
                [](y < 0 => x \in P)

\* Lazy function (FcnLambdaValue).
LazyFcn == \A P \in {LET K == {2049 - i : i \in 1..2048}
                     IN [n \in Nat |-> \E e \in K : e = n]} :
                [](y < 0 => P[x])

-----------------------------------------------------------

\* SpecProcessor#processConstantDefns evaluates the constant definitions below
\* once at startup, and all workers share the value of a definition. Workers
\* must not race to normalize a definition or its cache.

\* Enumerated in descending order.
EnumDef == {2049 - i : i \in 1..2048}

PredDef == {t \in ((1025..2048) \X {0}) \cup ((1..1024) \X {0}) : TRUE}

CupDef == ((1025..2048) \X {0}) \cup ((1..1024) \X {0})

UnionDef == UNION {1..2048, 2..2048}

LambdaDef == [t \in ((1025..2048) \X {0}) \cup ((1..1024) \X {0}) |-> t[1]]

DefCache == [](y < 0 => /\ x \in EnumDef
                        /\ PredDef # {} /\ \E e \in PredDef : e = <<x, 0>>
                        /\ CupDef # {} /\ \E e \in CupDef : e = <<x, 0>>
                        /\ UnionDef # {} /\ \E e \in UnionDef : e = x
                        /\ LambdaDef = LambdaDef /\ LambdaDef[<<x, 0>>] = x)

-----------------------------------------------------------

\* TLCEval caches the value of a constant-level expression in the empty
\* context, and all workers share the cached value.  Workers race to
\* normalize it when they enumerate it.  The enumeration of a lazy set (\cup)
\* is out of order, too.
EvalCache == [](y < 0 => /\ \E e \in TLCEval({2049 - i : i \in 1..2048}) : e = x
                         /\ \E e \in TLCEval(((1025..2048) \X {0}) \cup ((1..1024) \X {0})) :
                                e = <<x, 0>>)

-----------------------------------------------------------

\* The main thread (model checking) or the simulator evaluates Init, which
\* sets the register of every worker to the same value.  Workers race to
\* normalize the register when they enumerate it.
InitSet == Init /\ TLCSet(1, {2049 - i : i \in 1..2048})

SpecSet == InitSet /\ [][NextStutter]_vars

SetCache == [](y < 0 => \E e \in TLCGet(1) : e = x)

-----------------------------------------------------------

\* A worker sets its own register, which TLCGet("all") hands to all other
\* workers.  Workers race to normalize the register when they enumerate it.
\* InitAll sets the registers of all workers, so that none of them is
\* undefined.  NextAll sets a register before it enumerates x', so that each
\* initial state sets the register once.
InitAll == Init /\ TLCSet(1, {})

NextAll == \/ y > 0 /\ TLCSet(1, {2049 - i : i \in 1..2048})
                    /\ x' \in 1..2048 /\ y' = -y
           \/ y < 0 /\ UNCHANGED vars

SpecAll == InitAll /\ [][NextAll]_vars

AllCache == [](y < 0 => LET R == TLCGet("all")[1]
                        IN \A w \in DOMAIN R : R[w] = {} \/ \E e \in R[w] : e = x)

-----------------------------------------------------------

\* SpecProcessor unrolls the \A of each property below, which binds a lazy set
\* or function P in the context of an invariant.  P's domain Nat is infinite,
\* so P stays lazy.  P evaluates its body in the context in which TLC created
\* P, which binds T to the element of the set of sets in descending order.  No
\* LET or \A of the property binds T, so normalizing the context of the
\* invariant leaves T alone.  Workers race to normalize T when they
\* enumerate it.

\* Lazy set (SetPredValue).
CtxPred == \A P \in {{n \in Nat : \E e \in T : e = n} : T \in {{2049 - i : i \in 1..2048}}} :
                [](y < 0 => x \in P)

\* Lazy function (FcnLambdaValue).
CtxFcn == \A P \in {[n \in Nat |-> \E e \in T : e = n] : T \in {{2049 - i : i \in 1..2048}}} :
                [](y < 0 => P[x])

-----------------------------------------------------------

\* SpecProcessor#processConstantDefns evaluates the constant definition below
\* once at startup, and all workers share its value.  Tool converts the outer
\* function, whose domain is an interval, to a FcnRcdValue.  It leaves the
\* inner functions lazy (FcnLambdaValue), because their domain is a lazy set
\* (\X), and deepNormalize does not convert them either.  Thus, all workers
\* share 2048 lazy functions whose caches are empty.
LazyDefs == [i \in 1..2048 |-> [t \in (1..2) \X {0} |-> 0]]

\* The workers that generate the 8 successor states with the same x take the
\* EXCEPT of LazyDefs[x] repeatedly before they compare LazyDefs[x], which
\* caches its FcnRcdValue.  If another worker caches the FcnRcdValue between
\* FcnLambdaValue#takeExcept's check for the cache and the copy of
\* LazyDefs[x], the copy evaluates to the cache and ignores the EXCEPT.
ExceptDef == [](y < 0 => LET F == LazyDefs[x]
                         IN /\ \A k \in 1..256 : [F EXCEPT ![<<1, 0>>] = 1][<<1, 0>>] = 1
                            /\ F = F)
===========================================================
