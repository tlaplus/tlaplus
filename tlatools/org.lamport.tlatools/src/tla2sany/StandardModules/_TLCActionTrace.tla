------- MODULE _TLCActionTrace ------
LOCAL INSTANCE IOUtils
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE Sequences
LOCAL INSTANCE SequencesExt
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE FiniteSetsExt

LOCAL _extends ==
    LET M == FoldSet(LAMBDA a, acc: acc \cup {a[2].location.module}, 
            {}, CounterExample.action)
    IN FoldSet(LAMBDA module, acc: acc \o (IF acc = "" THEN "EXTENDS " ELSE ", ") \o module, 
                "", M)

LOCAL _next ==
    LET Params(r) == FoldLeft(LAMBDA acc, p: acc \o (IF acc = "" THEN "" ELSE ", ") \o ToString(r.context[p]), 
                              "", r.parameters)
        Signature(r) == IF "parameters" \in DOMAIN r THEN r.name \o "(" \o Params(r) \o ")" ELSE r.name
        ToDisjunct(i, r) == "\\/ " \o ToString(i) \o " = _idx /\\ " \o Signature(r) \o "\n"
    IN TLCLiteral(FoldSet(LAMBDA a, acc: acc \o ToDisjunct(a[1][1], a[2]), 
            "", CounterExample.action))

LOCAL _TLCTraceFile == "TLCActionTrace.tla"

LOCAL _TLCTraceModule ==
	LET ModuleName == ReplaceFirstSubSeq("", ".tla", _TLCTraceFile) 
        L == ToString(Cardinality(CounterExample.action)) IN
	"---- MODULE " \o ModuleName \o " ----\n" \o
	 \*TODO callsignature symbols may not be defined in the same modules where the actions are defined.
	 \*TODO E.g., model values are typically defined in the MC file.
        _extends \o "\n\n" \o
    "_length == " \o L \o "\n\n" \o
    "_next(_idx) ==\n" \o
	    ToString(_next) \o "\n" \o
    "_actionConstraint ==\n" \o
    "_next(LET T == INSTANCE TLC IN T!TLCGet(\"level\"))\n" \o
    "\n===="

LOCAL _TLCTrace ==
    IF CounterExample.action = {} THEN TRUE ELSE
        /\ Serialize(_TLCTraceModule,
    			_TLCTraceFile,
    			[
    				format |-> "TXT",
    				charset |-> "UTF-8",
    				openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>
    			]
           ).exitValue = 0
        /\ PrintT("CounterExample written: " \o _TLCTraceFile)

======