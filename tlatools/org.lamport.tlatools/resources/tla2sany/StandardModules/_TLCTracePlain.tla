----------------------- MODULE _TLCTracePlain ------------------------
LOCAL INSTANCE IOUtils
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE Sequences
LOCAL INSTANCE SequencesExt

LOCAL _TLCTraceFile ==
    "CounterExample.tlc"

LOCAL _TLCTraceModule ==
	LET ModuleName == ReplaceFirstSubSeq("", ".tla", _TLCTraceFile) IN
	"---- MODULE " \o ModuleName \o " ----\n" \o
    "LOCAL INSTANCE TLC\n\n" \o
    "Trace == \n\t" \o
	ToString(ToTrace(CounterExample)) \o
    "\n\n===="

LOCAL _TLCTrace ==
    IF CounterExample.state = {} THEN TRUE ELSE
        /\ Serialize(_TLCTraceModule,
    			_TLCTraceFile,
    			[
    				format |-> "TXT",
    				charset |-> "UTF-8",
    				openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>
    			]
           ).exitValue = 0
        /\ PrintT("CounterExample written: " \o _TLCTraceFile)

=============================================================================
