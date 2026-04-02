------------------------------- MODULE _JsonTrace -------------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE Json
LOCAL INSTANCE Sequences

CONSTANT _JsonTraceFile

_JsonTrace ==
    IF CounterExample.state = {} \/ ("console" \in DOMAIN CounterExample /\ CounterExample["console"] = FALSE) THEN TRUE ELSE
        /\ LET trace == ToTrace(CounterExample)
               vars  == UNION { DOMAIN trace[i] : i \in DOMAIN trace }
           IN JsonSerialize(_JsonTraceFile, [counterexample |-> CounterExample, vars |-> vars])
        /\ PrintT("CounterExample written: " \o _JsonTraceFile)

----------------------------------------------------------------------------
\* Deserialize a trace created by _JsonTrace above.

CONSTANT _JsonTraceInputFile   \* Used by -loadTrace json

\* This operator has a Java module override (tlc2.module._JsonTrace#tlcState).
LOCAL _TLCState(level) ==
	Trace[level]

LOCAL _JsonTraceConstraint ==
    LET level == TLCGet("level")
        dump  == JsonDeserialize(_JsonTraceInputFile)
        \* DOMAIN trace is meaningful only because we serialize TLA+ sets as JSON arrays. JSON has
        \* no set type---only the world's favorite least-common-denominator of strings, numbers,
        \* and nested lists---so on the wire every set is an ordered sequence. If that encoding
        \* ever changed (or JSON miraculously grew a real set type), indexing states by DOMAIN
        \* would stop matching what we dump.
        \* Rebuilding vars likewise assumes the array order matches TLC's normalized set order from
        \* when the trace was written; the format does not pin down a stronger invariant.
        trace == dump["counterexample"]["state"]
        \* JSON deserializes sets as tuples, so convert back to a set
        vars  == {dump["vars"][i] : i \in DOMAIN dump["vars"]}
	\* For liveness properties, TLC trace dumps stop at the state *before* the
	\* lasso is closed. When replaying such a trace, TLC may request a state with
	\*   level = Len(dump) + 1,
	\* which does not exist in the dump. In that case, the constraint
	\* is intentionally vacuously satisfied.
	\* Since the names of the spec's variables are not known, Trace[level] is
	\* used as a generic reference to the variables of the current state.
    IN level \in DOMAIN trace =>
            \* When loading a trace with a subset of variables, only check the variables
            \* that exist in both the trace and the current state. This allows trace 
            \* replay with specs that have different variable sets than the original spec
            \* that produced the trace. Another scenario is when the spec uses ALIAS
            \* to rename, add, or remove variables.
            \A v \in vars \cap (DOMAIN _TLCState(level)):
                    _TLCState(level)[v] = trace[level][2][v]

=============================================================================
