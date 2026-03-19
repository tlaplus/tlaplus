------------------------------ MODULE ACP_SB_TLC -------------------------------

\* ACP_SB, TLC ready

EXTENDS ACP_SB, TLC

Perms == Permutations(participants) \* to benefit from symmetries

--------------------------------------------------------------------------------

\* AC4 rewritten in a way that is better handled by TLC

AC4_alt == [][ /\ (\A i \in participants : participant[i].decision = commit 
                                => (participant'[i].decision = commit))
               /\ (\A j \in participants : participant[j].decision = abort  
                                => (participant'[j].decision = abort))]_<<participant>>

================================================================================
