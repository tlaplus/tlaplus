------------------------------- MODULE _JsonTrace -------------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE Json
LOCAL INSTANCE Sequences

CONSTANT _JsonTraceFile

_JsonTrace ==
    IF CounterExample.state = {} \/ ("console" \in DOMAIN CounterExample /\ CounterExample["console"] = FALSE) THEN TRUE ELSE
        /\ JsonSerialize(_JsonTraceFile, CounterExample)
        /\ PrintT("CounterExample written: " \o _JsonTraceFile)

----------------------------------------------------------------------------
\* Deserialize a trace created by _JsonTrace above.

\* This operator has a Java module override (tlc2.module._JsonTrace#tlcState).
LOCAL _TLCState(level) ==
	Trace[level]

LOCAL _JsonTraceConstraint ==
    LET level == TLCGet("level")
        dump  == JsonDeserialize(_JsonTraceFile)
    IN level \in DOMAIN dump.state => _TLCState(level) = dump.state[level][2]

=============================================================================
