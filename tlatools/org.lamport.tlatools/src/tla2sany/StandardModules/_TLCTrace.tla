---------------------------- MODULE _TLCTrace ----------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals

\* This operator has a Java module override (tlc2.module._TLCTrace#ioDeserialize).
LOCAL _TLCTraceDeserialize(absoluteFilename) ==
    TRUE

\* This operator has a Java module override (tlc2.module._TLCTrace#ioSerialize).
LOCAL _TLCTraceSerialize(val, absoluteFilename) ==
    TRUE

----------------------------------------------------------------------------
\* Serialize a trace to a file.

CONSTANT _TLCTraceFile

LOCAL _TLCTrace0(verbose) ==
    IF CounterExample.state = {} \/ ("console" \in DOMAIN CounterExample /\ CounterExample["console"] = FALSE) THEN TRUE ELSE
        /\ LET trace == ToTrace(CounterExample)
               vars  == UNION { DOMAIN trace[i] : i \in DOMAIN trace }
           IN _TLCTraceSerialize([counterexample |-> CounterExample, vars |-> vars], _TLCTraceFile)
        /\ IF verbose THEN PrintT("CounterExample written: " \o _TLCTraceFile) ELSE TRUE

LOCAL _TLCTraceSilent ==
    _TLCTrace0(FALSE)

_TLCTrace ==
    _TLCTrace0(TRUE)

----------------------------------------------------------------------------
\* Deserialize a trace created by _TLCTrace above.

CONSTANT _TLCTraceInputFile   \* Used by -loadTrace tlc

LOCAL _TLCTraceFileDeserialized ==
    _TLCTraceDeserialize(_TLCTraceInputFile)

\* This operator has a Java module override (tlc2.module._TLCTrace#tlcState).
LOCAL _TLCState(level) ==
	Trace[level]

\* A liveness counterexample's action graph contains a closing edge that
\* completes the lasso. In a forward path s1->s2->...->sn every edge
\* satisfies target[1] > source[1]; the closing edge is the unique edge
\* where target[1] <= source[1] (back-to-state: <, stuttering: =).
LOCAL _TLCTraceLassoTarget ==
    LET actions == _TLCTraceFileDeserialized["counterexample"]["action"]
    IN IF \E e \in actions : e[3][1] <= e[1][1]
       THEN (CHOOSE e \in actions : e[3][1] <= e[1][1])[3][1]
       ELSE 0

LOCAL _TLCTraceConstraint ==
    LET level == TLCGet("level")
        dump  == _TLCTraceFileDeserialized
        trace == dump["counterexample"]["state"]
        vars  == dump["vars"]
	\* The trace (CounterExample.state) is a set of <<level, state>> pairs,
	\* not a function/sequence.
	\* For liveness properties, TLC trace dumps stop at the state *before* the
	\* lasso is closed. When replaying such a trace, TLC may request a state with
	\* a level that does not exist in the dump. In that case, no pair matches and
	\* the implication is vacuously satisfied.
    IN \A pair \in trace:
            pair[1] = level =>
                \* When loading a trace with a subset of variables, only check the
                \* variables that exist in both the trace and the current state.
                \* This allows trace replay with specs that have different variable
                \* sets than the original spec that produced the trace. Another
                \* scenario is when the spec uses ALIAS to rename, add, or remove
                \* variables.
                \A v \in vars \cap DOMAIN _TLCState(level):
                        _TLCState(level)[v] = pair[2][v]

\* VIEW for trace replay. Includes TLCGet("level") to prevent premature
\* state collapsing within the trace. For liveness traces, the level
\* beyond the trace is mapped to the lasso target so the cycle can close.
LOCAL _TLCTraceView ==
    LET level       == TLCGet("level")
        trace       == _TLCTraceFileDeserialized["counterexample"]["state"]
        lassoTarget == _TLCTraceLassoTarget
    IN IF \E pair \in trace : pair[1] = level
       THEN << level, _TLCState(level) >>
       ELSE << lassoTarget, _TLCState(level) >>

=============================================================================
