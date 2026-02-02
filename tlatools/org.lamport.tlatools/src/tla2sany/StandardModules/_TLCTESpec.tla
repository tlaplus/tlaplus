----------------------- MODULE _TLCTESpec ------------------------
LOCAL INSTANCE IOUtils
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE Sequences
LOCAL INSTANCE SequencesExt
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE FiniteSetsExt

LOCAL _extends ==
    LET M == FoldSet(LAMBDA a, acc: acc \cup {a[2].location.module}, {}, CounterExample.action)
    IN FoldSet(LAMBDA module, acc: acc \o (IF acc = "" THEN "EXTENDS " ELSE ", ") \o module, "", M)

LOCAL _Vars ==
    UNION { DOMAIN pair[2] : pair \in CounterExample.state }

LOCAL _ToConjunt(v, prime, idx) ==
    "/\\ " \o v \o prime \o " = Trace[" \o idx \o "]." \o v \o "\n"

CONSTANT _TLCTraceOutputFile  \* Used by -dumpTrace tlcTESpec

LOCAL _conjunct(prime, idx) ==
    FoldSet(LAMBDA v, acc: acc \o _ToConjunt(v, prime, idx), "", _Vars)

LOCAL _subVars ==
    FoldSet(LAMBDA v, acc: acc \o (IF acc = "" THEN "" ELSE ", ") \o v, "", _Vars)

LOCAL _TLCTraceModule ==
	LET ModuleName == ReplaceFirstSubSeq("", ".tla", _TLCTraceOutputFile) IN
	"---- MODULE " \o ModuleName \o " ----\n" \o
	 \*TODO E.g., model values are typically defined in the MC file.
        _extends \o "\n\n" \o
    "LOCAL INSTANCE TLC\n\n" \o
    "Trace == \n\t" \o
	ToString(ToTrace(CounterExample)) \o
	"\n\n" \o
    "_init ==\n" \o _conjunct("", "1") \o
	"\n" \o
    "_next ==\n\\E i,j \\in DOMAIN Trace:\n/\\ i = TLCGet(\"level\")\n/\\ j = i + 1\n" \o
    _conjunct("", "i") \o _conjunct("'", "j") \o
    "\n(* Allow infinite stuttering to prevent deadlock on termination. *)" \o
    "\n_terminating ==\n\tUNCHANGED <<" \o _subVars \o ">>" \o 
    "\n\n_spec == \n\t_init /\\ [][_next \\/ _terminating]_<<" \o _subVars \o ">>\n" \o
    "\n===="
    \* TODO: Append in-file config here.

_TLCTrace ==
    IF CounterExample.state = {} \/ ("console" \in DOMAIN CounterExample /\ CounterExample["console"] = FALSE) THEN TRUE ELSE
        /\ Serialize(_TLCTraceModule,
    			_TLCTraceOutputFile,
    			[
    				format |-> "TXT",
    				charset |-> "UTF-8",
    				openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>
    			]
           ).exitValue = 0
        /\ PrintT("CounterExample written: " \o _TLCTraceOutputFile)

=============================================================================
