------------------------------- MODULE _TransitTrace -------------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE Transit
LOCAL INSTANCE Sequences

LOCAL _TransitTraceFile ==
    "CounterExample.transit"

LOCAL _TransitTrace ==
    IF CounterExample.state = {} THEN TRUE ELSE
        /\ TransitSerialize(_TransitTraceFile, ToTrace(CounterExample))
        /\ PrintT("CounterExample written: " \o _TransitTraceFile)

=============================================================================
