--------------------------------- MODULE CalculatorSC ---------------------------------
EXTENDS TLC, IOUtils, Integers, Sequences

N ==
    TLCGet("revision").tag

B ==
    <<"-simulate", "num=25000", "-depth", "1000">>

Cmd == LET absolutePathOfTLC == TLCGet("config").install
       IN <<"java", 
          "-Dtlc2.tool.Simulator.extendedStatistics=true",
          "-Dtlc2.tool.Simulator.extendedStatistics.naive=true",
          "-cp",
          absolutePathOfTLC,
          "tlc2.TLC",
          "-noTE",
          "-fp", "0", "-seed", "0",
          "-config", "Calculator.cfg",
          "Calculator.tla">> \o B

\* Baseline
ASSUME
    LET ret == IOEnvExec([R |-> -1, N |-> N], Cmd).exitValue
    IN CASE ret =  0 -> PrintT("baseline")
         [] OTHER    -> Print(<<IOEnvExec([R |-> -1, N |-> N], Cmd), "Error">>, FALSE)

-----------------------------------------------------------------------------

RLCmd == LET absolutePathOfTLC == TLCGet("config").install
         IN <<"java", 
            "-Dtlc2.tool.Simulator.rl=true",
            "-Dtlc2.tool.Simulator.extendedStatistics=true",
            "-Dtlc2.tool.Simulator.extendedStatistics.naive=true",
            "-cp",
            absolutePathOfTLC,
            "tlc2.TLC",
            "-noTE",
            "-fp", "0", "-seed", "0",
            "-config", "Calculator.cfg",
            "Calculator.tla">> \o B

ASSUME \A reward \in { -200, -100, -10, -1, 0, 1, 10, 100 }:
    LET ret == IOEnvExec([N |-> N, R |-> reward], RLCmd).exitValue
    IN CASE ret =  0 -> PrintT(reward)
         [] OTHER    -> Print(<<reward, IOEnvExec([N |-> N, R |-> reward], RLCmd), "Error">>, FALSE)

=============================================================================
---- CONFIG CalculatorSC ----
\* TLC always expects a configuration file, but an empty one will do in this case.
\* If this approach proves useful, TLC should be extended to launch without a config
\* file.
====