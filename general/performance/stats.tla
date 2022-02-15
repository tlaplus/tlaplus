----------------------------- MODULE stats -----------------------------
EXTENDS TLC, Integers, Sequences, IOUtils, CSV

\* Filename for the CSV file that appears also in the R script and is passed
\* to the nested TLC instances that are forked below.
CSVFile ==
    "out_run-stats.csv"

\* Write column headers to CSV file at startup of TLC instance that "runs"
\* this script and forks the nested instances of TLC that simulate the spec
\* and collect the statistics.
ASSUME 
    (CSVRecords(CSVFile) = 0) =>
        CSVWrite("Spec#Run#Timestamp#RevTS#RevTag#RevDate#Workers#Diameter#Generated#Distinct#Queue#Duration",
             <<>>, CSVFile)

PostCondition ==
    CSVWrite("%1$s#%2$s#%3$s#%4$s#%5$s#%6$s#%7$s#%8$s#%9$s#%10$s#%11$s#%12$s",
            <<  IOEnv.spec,
                IOEnv.run,
                IOEnv.timestamp,

                TLCGet("revision").timestamp,
                TLCGet("revision").tag,
                TLCGet("revision").date,

                TLCGet("config").worker,

                TLCGet("diameter"),
                TLCGet("generated"),
                TLCGet("distinct"),
                TLCGet("queue"),
                TLCGet("duration")
            >>, CSVFile)

=============================================================================
