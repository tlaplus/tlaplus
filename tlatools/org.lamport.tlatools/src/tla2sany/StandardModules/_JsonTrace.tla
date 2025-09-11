------------------------------- MODULE _JsonTrace -------------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE Json
LOCAL INSTANCE Sequences

LOCAL _DumpTraceFilePrefix == ""

LOCAL _JsonTraceFile ==
    "CounterExample.json"

LOCAL _JsonTrace ==
    IF CounterExample.state = {} THEN TRUE ELSE
        /\ JsonSerialize(_DumpTraceFilePrefix \o _JsonTraceFile, CounterExample)
        /\ PrintT("CounterExample written: " \o _DumpTraceFilePrefix \o _JsonTraceFile)

=============================================================================
