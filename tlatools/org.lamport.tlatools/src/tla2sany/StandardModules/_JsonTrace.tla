------------------------------- MODULE _JsonTrace -------------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE Json
LOCAL INSTANCE Sequences

LOCAL _DumpTraceFile == ""

LOCAL _JsonTrace ==
    IF CounterExample.state = {} THEN TRUE ELSE
        /\ JsonSerialize(_DumpTraceFile, CounterExample)
        /\ PrintT("CounterExample written: " \o _DumpTraceFile)

=============================================================================
