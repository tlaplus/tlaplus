------------------------------- MODULE _DotTrace -------------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE GraphViz
LOCAL INSTANCE IOUtils
LOCAL INSTANCE Sequences
LOCAL INSTANCE Functions

CONSTANT _DotTraceFile

_DotTrace ==
    IF CounterExample.state = {} THEN TRUE ELSE
        /\ LET N == CounterExample.state
               E == { <<e[1], e[3], e[2]>> : e \in CounterExample.action }
               G == [node |-> N, edge |-> E] IN
           Serialize(DotDiGraph(G, LAMBDA v: FoldFunctionOnSet(
           								LAMBDA x, y: ToString(x) \o "\n" \o y, "", v[2], DOMAIN v[2]), 
           						   LAMBDA e: e[3].name),
    			_DotTraceFile,
    			[
    				format |-> "TXT",
    				charset |-> "UTF-8",
    				openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>
    			]
           ).exitValue = 0
        /\ PrintT("CounterExample written: " \o _DotTraceFile)

=============================================================================
