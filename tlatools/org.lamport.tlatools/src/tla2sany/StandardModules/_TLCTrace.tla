---------------------------- MODULE _TLCTrace ----------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE Sequences
LOCAL INSTANCE IOUtils

LOCAL _TLCTraceFile ==
    "CounterExample.tlc"

LOCAL _TLCTrace ==
    IF CounterExample.state = {} THEN TRUE ELSE
        /\ IOSerialize(ToTrace(CounterExample), _TLCTraceFile, TRUE)
        /\ PrintT("CounterExample written: " \o _TLCTraceFile)

=============================================================================
