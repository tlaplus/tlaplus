---------------------------- MODULE _TLCTrace ----------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE Sequences

LOCAL _TLCTraceSerialize(val, absoluteFilename) ==
    TRUE

CONSTANT _TLCTraceFile

LOCAL _TLCTraceSilent ==
    IF CounterExample.state = {} THEN TRUE ELSE
        /\ _TLCTraceSerialize(ToTrace(CounterExample), _TLCTraceFile)

_TLCTrace ==
    IF CounterExample.state = {} THEN TRUE ELSE
        /\ _TLCTraceSerialize(ToTrace(CounterExample), _TLCTraceFile)
        /\ PrintT("CounterExample written: " \o _TLCTraceFile)

----------------------------------------------------------------------------
\* Deserialize a trace created by _TLCTrace above.

\* This operator has a Java module override (tlc2.module._TLCTrace#ioDeserialize).
LOCAL _TLCTraceDeserialize(absoluteFilename) ==
    TRUE

\* This operator has a Java module override (tlc2.module._TLCTrace#tlcTraceConstraint0).
LOCAL _TLCTraceConstraint0(absoluteFilename) ==
    LET level == TLCGet("level")
        dump  == _TLCTraceDeserialize(absoluteFilename)
	\* For liveness properties, TLC trace dumps stop at the state *before* the
	\* lasso is closed. When replaying such a trace, TLC may request a state with
	\*   level = Len(dump) + 1,
	\* which does not exist in the dump. In that case, the constraint
	\* is vacuously satisfied.
	\* Since the names of the spec’s variables are not known, Trace[level] is
	\* used as a generic reference to the variables of the current state.
    IN level \in DOMAIN dump => Trace[level] = dump[level]

LOCAL _TLCTraceConstraint ==
    _TLCTraceConstraint0(_TLCTraceFile)

=============================================================================
