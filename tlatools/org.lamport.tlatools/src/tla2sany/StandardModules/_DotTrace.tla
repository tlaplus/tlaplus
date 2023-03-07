------------------------------- MODULE _DotTrace -------------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE GraphViz
LOCAL INSTANCE IOUtils
LOCAL INSTANCE Sequences

LOCAL _DotTraceFile ==
    "CounterExample.Dot"

LOCAL _DotTrace ==
    IF CounterExample.state = {} THEN TRUE ELSE
        /\ LET N == CounterExample.state
               E == { <<e[1], e[3], e[2]>> : e \in CounterExample.action }
               G == [node |-> N, edge |-> E] IN
           Serialize(DotDiGraph(G, LAMBDA v : ToString(v[2]), LAMBDA e: ToString(e[3].name)),
    			_DotTraceFile,
    			[
    				format |-> "TXT",
    				charset |-> "UTF-8",
    				openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>
    			]
           ).exitValue = 0
        /\ PrintT("CounterExample written: " \o _DotTraceFile)

=============================================================================
