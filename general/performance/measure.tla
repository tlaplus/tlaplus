Run with (single worker guarantees that the benachmarks run sequentially):

  $ wget https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar
  $ java -jar tla2tools.jar -workers 1 -config measure.tla measure.tla

----------------------------- MODULE measure -----------------------------
EXTENDS TLC, Integers, Sequences, IOUtils

AbsolutePathOfTLC == 
    TLCGet("config").install

Timestamp ==
    JavaTime

CmdTemplate ==
    <<"bash",
    "-c",
    "java " \o
    "-XX:+UseParallelGC " \o
    \* "-XX:MaxDirectMemorySize=20g -Xmx8g " \o
    \* "-Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet " \o
    \* Give 10 minutes to each run.
    "-Dtlc2.TLC.stopAfter=600 " \o
    "-DTLA-Library=.. " \o
    "-DspecName=%3$s " \o
    "-cp %1$s " \o
    "tlc2.TLC " \o
    "-checkpoint 0 -workers %2$s %3$s/MC.tla > %4$s 2>&1">>

LogFile(run, workers, spec) ==
    "out_run-" \o ToString(run) \o "_workers-" \o ToString(workers) \o "_spec-" \o spec \o ".txt"

-----------------------------------------------------------------------------

Specs ==
	{"Bloemen", "EWD840", "Ghostferry", "Grid5k", 
	 "MongoRepl", "PaxosCommit", "PaxosMadeSimple", "SwarmKit", "Bookkeeper"}

VARIABLE run, workers, spec, proc

Init ==
    /\ run \in 1..2
    /\ workers \in { 2^n : n \in 1..3 }
    /\ spec \in Specs
    /\ proc = [exitValue |-> -42, stdout |-> "", stderr |-> ""]

SafetyViolation ==
    /\ proc.exitValue = 12
    /\ PrintT(<<"run", run, "workers", workers, "spec", spec, "Safety violation">>)
    /\ UNCHANGED <<run, workers, spec, proc>>

LivenessViolation ==
    /\ proc.exitValue = 13
    /\ PrintT(<<"run", run, "workers", workers, "spec", spec, "Liveness violation">>)
    /\ UNCHANGED <<run, workers, spec, proc>>

Other ==
    /\ proc.exitValue \notin {-42, 0, 12, 13}
    /\ PrintT(<<"run", run, "workers", workers, "spec", spec, "Other violation">>)
    /\ UNCHANGED <<run, workers, spec, proc>>

ExecTLC ==
    /\ proc.exitValue = -42
    /\ PrintT(<<"run", run, "workers", workers, "spec", spec, "Starting">>)
    \*/\ PrintT(<<AbsolutePathOfTLC, ToString(workers), spec, LogFile(run, workers, spec)>>)
    /\ proc' = IOEnvExecTemplate(
                [ 
                    run |-> run,
                    spec |-> spec,
                    timestamp |-> Timestamp
                ],
                CmdTemplate, 
                <<AbsolutePathOfTLC, ToString(workers), spec, LogFile(run, workers, spec)>> )
    /\ UNCHANGED <<run, workers, spec>>

Done ==
    /\ proc.exitValue = 0
    /\ PrintT(<<"run", run, "spec", "workers", workers, spec, "Done">>)
    /\ UNCHANGED <<run, workers, spec, proc>>

Next ==
    \/ ExecTLC
    \/ Done
    \/ LivenessViolation
    \/ SafetyViolation
    \/ Other

=============================================================================
---- CONFIG measure ----
INIT Init
NEXT Next
CHECK_DEADLOCK FALSE
====