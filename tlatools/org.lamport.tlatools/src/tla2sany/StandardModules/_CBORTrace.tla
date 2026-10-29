------------------------------- MODULE _CBORTrace -------------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE CBOR
LOCAL INSTANCE Sequences

CONSTANT _CBORTraceFile

_CBORTrace ==
    IF CounterExample.state = {} \/ ("console" \in DOMAIN CounterExample /\ CounterExample["console"] = FALSE) THEN TRUE ELSE
        /\ LET trace == ToTrace(CounterExample)
               vars  == UNION { DOMAIN trace[i] : i \in DOMAIN trace }
           IN CBORSerialize(_CBORTraceFile, [counterexample |-> CounterExample, vars |-> vars])
        /\ PrintT("CounterExample written: " \o _CBORTraceFile)

=============================================================================
