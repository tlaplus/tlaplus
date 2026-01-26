----------------------- MODULE _TLCTracePlain ------------------------
LOCAL INSTANCE IOUtils
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE Sequences
LOCAL INSTANCE SequencesExt

CONSTANT _TLCTraceFile

LOCAL _TLCTraceModule ==
	LET ModuleName == ReplaceFirstSubSeq("", ".tla", _TLCTraceFile) IN
	"---- MODULE " \o ModuleName \o " ----\n" \o
    "LOCAL INSTANCE TLC\n\n" \o
    "Trace == \n\t" \o
	ToString(ToTrace(CounterExample)) \o
    "\n\n===="

_TLCTrace ==
    IF CounterExample.state = {} \/ ("console" \in DOMAIN CounterExample /\ CounterExample["console"] = FALSE) THEN TRUE ELSE
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
