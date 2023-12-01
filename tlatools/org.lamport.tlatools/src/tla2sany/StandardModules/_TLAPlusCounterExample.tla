----------------------- MODULE _TLAPlusCounterExample ------------------------
LOCAL INSTANCE IOUtils
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE Sequences
LOCAL INSTANCE SequencesExt

LOCAL _TLAPlusCounterExampleFile ==
    "CounterExample.tla"

LOCAL _TLAPlusCounterExampleModule ==
	LET ModuleName == ReplaceFirstSubSeq("", ".tla", _TLAPlusCounterExampleFile) IN
	"---- MODULE " \o ModuleName \o " ----\n" \o
    "LOCAL INSTANCE TLC\n\n" \o
    "CounterExample == \n\t" \o
    ToString(CounterExample) \o 
    "\n\n===="

LOCAL _TLAPlusCounterExample ==
    IF CounterExample.state = {} THEN TRUE ELSE
        /\ Serialize(_TLAPlusCounterExampleModule,
    			_TLAPlusCounterExampleFile,
    			[
    				format |-> "TXT",
    				charset |-> "UTF-8",
    				openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>
    			]
           ).exitValue = 0
        /\ PrintT("CounterExample written: " \o _TLAPlusCounterExampleFile)

=============================================================================
