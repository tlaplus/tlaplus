-------------------------- MODULE ChooseTableauSymmetry --------------------------
CONSTANT Val
VARIABLE arr

Init == arr = [v \in Val |-> "ready"]

Ready(v) == /\ arr[v] = "ready"
            /\ arr' = [arr EXCEPT ![v]= "busy"]

Busy(v) == /\ arr[v] = "busy"
           /\ arr' = [arr EXCEPT ![v]= "done"]

Done(v) == /\ arr[v] = "done"
           /\ arr' = [arr EXCEPT ![v]= "ready"]

Next == \E v \in Val : Ready(v) \/ Busy(v) \/ Done(v)

Spec == Init /\[][Next]_<<arr>> /\ WF_<<arr>>(Next)

Some     == CHOOSE e \in Val: TRUE
Other(v) == CHOOSE e \in Val \ {v}: TRUE

Liveness  == LET v == Some
             IN (arr[v] = "busy") ~> (arr[v] = "ready")

LivenessO == LET v == Other(Some)
             IN (arr[v] = "busy") ~> (arr[v] = "ready")

=============================================================================
