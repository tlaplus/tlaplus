
Run the following to collect data before plotting the R script.

  $ tlc Counter -note -depth 50 -fp 1 -simulate num=50000
  $ tlc Counter -note -depth 50 -fp 1 -simulate num=50000,sched=rl


------ MODULE Counter ------
EXTENDS Integers, CSV, TLC, TLCExt

VARIABLE x

Init ==
    x = 0

Add == x' = x + 1
Sub == x' = x - 1



Divide == x' = x \div 2
Multiply == x' = x * 2



Reset == x' = 0

Next ==
    \/ Add
    \/ Sub
    \/ Reset
    \/ Multiply
    \/ Divide

---------------------------

ASSUME TLCGet("config").sched \in {"rl", "random"}

CSVFile == "Counter.csv"

CSVColumnHeaders ==
    "Mode#Time#Val#Action"

ASSUME
    CSVRecords(CSVFile) = 0 => 
        CSVWrite(CSVColumnHeaders, <<>>, CSVFile)

StatisticsStateConstraint ==
    \* (TLCGet("level") > TLCGet("config").depth) =>
        TLCDefer(CSVWrite("%1$s#%2$s#%3$s#%4$s",
                << TLCGet("config").sched,TLCGet("stats").generated,x,TLCGet("action").name>>, CSVFile))

=====