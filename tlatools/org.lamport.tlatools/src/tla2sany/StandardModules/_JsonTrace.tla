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

=============================================================================
