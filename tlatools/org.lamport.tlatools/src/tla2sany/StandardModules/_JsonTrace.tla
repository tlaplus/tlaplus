------------------------------- MODULE _JsonTrace -------------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE Json
LOCAL INSTANCE Sequences

CONSTANT _JsonTraceFile

LOCAL _JsonTrace ==
    IF CounterExample.state = {} THEN TRUE ELSE
        /\ JsonSerialize(_JsonTraceFile, CounterExample)
        /\ PrintT("CounterExample written: " \o _JsonTraceFile)

=============================================================================
