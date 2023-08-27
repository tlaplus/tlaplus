------------------- MODULE Calculator ----------------------
EXTENDS Integers, CSV, TLC, IOUtils

VARIABLE x

Init ==
    x = 0

Inc ==
    x' = x + 1

Dec ==
    x' = x - 1

Mul ==
    x' = x * 2

Div ==
    x' = x \div 2

Rst ==
    x' = 0

Stutt ==
    x' = x

Dis ==
    /\ x < 0
    /\ x' = x * (-1)
    
Next ==
    \/ Inc
    \/ Dec
    \/ Mul
    \/ Div
    \/ Rst
\*    \/ Stutt
\*    \/ Dis

------------------------------------------------------------

Reward ==
	atoi(IOEnv.R)

Stats ==
    LET conf   == [ e \in {"mode", "sched", "depth"} |-> TLCGet("config")[e] ]
        stats  == [ e \in {"traces", "duration", "generated", "distinct", "retries", "levelmean", "levelvariance"} |-> TLCGet("stats")[e] ]
        actions == TLCGet("stats").actions
    IN CSVWriteRecord([ts|-> JavaTime, note |-> IOEnv.N, reward |-> atoi(IOEnv.R)] @@ conf @@ stats @@ actions, "#", CSVRecords("Calculator.csv") = 0, "Calculator.csv")

============================================================