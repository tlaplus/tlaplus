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
===========================================================
