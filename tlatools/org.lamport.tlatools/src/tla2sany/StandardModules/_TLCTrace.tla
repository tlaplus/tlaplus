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

LOCAL _TLCTrace ==
    IF CounterExample.state = {} THEN TRUE ELSE
        /\ _TLCTraceSerialize(ToTrace(CounterExample), _TLCTraceFile)
        /\ PrintT("CounterExample written: " \o _TLCTraceFile)

=============================================================================
