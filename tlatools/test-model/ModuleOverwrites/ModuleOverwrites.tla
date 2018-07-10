-------------------------- MODULE ModuleOverwrites --------------------------
EXTENDS Integers, Sequences

VARIABLES t

Init == t = [ i \in 1..10 |-> i ]

Next == t' = t

-----------------------------------------------------------------------------

noDupesOverwrite(arr, emp) == FALSE

InvAsModuleOverwrite == noDupesOverwrite(t, -1)

-----------------------------------------------------------------------------

noDupesOverwriteLinear(arr, emp) == FALSE

InvAsModuleOverwriteLinear == noDupesOverwriteLinear(t, -1)

-----------------------------------------------------------------------------

noDupes(arr, emp) == LET sub == SelectSeq(t, LAMBDA e: e # -1)
                         abs(number) == IF number < 0 THEN -1 * number ELSE number
                     IN IF Len(sub) < 2 THEN TRUE
                        ELSE \A i \in 1..(Len(sub) - 1):
                                \A j \in (i+1)..Len(sub):
                                   abs(sub[i]) # abs(sub[j]) 

InvNoModuleOverwrite == noDupes(t, -1)
=============================================================================
