-------------------- MODULE Github1445 --------------------
EXTENDS Integers
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
===========================================================
