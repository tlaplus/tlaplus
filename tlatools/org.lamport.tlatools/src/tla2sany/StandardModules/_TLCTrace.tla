---------------------------- MODULE _TLCTrace ----------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE Sequences

LOCAL _TLCTraceSerialize(val, absoluteFilename) ==
    TRUE

CONSTANT _TLCTraceFile

LOCAL _TLCTrace0(verbose) ==
    IF CounterExample.state = {} \/ ("console" \in DOMAIN CounterExample /\ CounterExample["console"] = FALSE) THEN TRUE ELSE
        /\ _TLCTraceSerialize(ToTrace(CounterExample), _TLCTraceFile)
        /\ IF verbose THEN PrintT("CounterExample written: " \o _TLCTraceFile) ELSE TRUE

LOCAL _TLCTraceSilent ==
    _TLCTrace0(FALSE)

_TLCTrace ==
    _TLCTrace0(TRUE)

=============================================================================
