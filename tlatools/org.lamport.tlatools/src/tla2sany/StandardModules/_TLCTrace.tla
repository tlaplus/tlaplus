---------------------------- MODULE _TLCTrace ----------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE Sequences

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
           IN _TLCTraceSerialize([trace |-> trace, vars |-> vars], _TLCTraceFile)
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

LOCAL _TLCTraceConstraint ==
    LET level == TLCGet("level")
        dump  == _TLCTraceFileDeserialized
        trace == dump["trace"]
        vars  == dump["vars"]
	\* For liveness properties, TLC trace dumps stop at the state *before* the
	\* lasso is closed. When replaying such a trace, TLC may request a state with
	\*   level = Len(dump) + 1,
	\* which does not exist in the dump. In that case, the constraint
	\* is intentionally vacuously satisfied.
	\* Since the names of the spec’s variables are not known, Trace[level] is
	\* used as a generic reference to the variables of the current state.
    IN level \in DOMAIN trace => 
            \* When loading a trace with a subset of variables, only check the variables
            \* that exist in both the trace and the current state. This allows trace 
            \* replay with specs that have different variable sets than the original spec
            \* that produced the trace. Another scenario is when the spec uses ALIAS
            \* to rename, add, or remove variables.
            \A v \in vars \cap DOMAIN _TLCState(level): 
                    _TLCState(level)[v] = trace[level][v]

=============================================================================
