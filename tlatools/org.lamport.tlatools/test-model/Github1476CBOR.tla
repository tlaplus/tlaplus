---------------------------- MODULE Github1476CBOR ----------------------------
EXTENDS TLC, TLCExt, CBOR

ReadsBack ==
    CBORDeserialize("states/Github1476.cbor")
        = [counterexample |-> CounterExample, vars |-> {"s", "q", "f"}]

==========================================================================
