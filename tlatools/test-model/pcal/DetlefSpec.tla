----------------------------- MODULE DetlefSpec ----------------------------- 
EXTENDS Sequences, Naturals

CONSTANTS Val, Procs, null


(* --algorithm Spec {
      variable queue = << >> ;
      process (P \in Procs) 
      variable rV = null ; {
L1: while (TRUE) {
      either 
        with (v \in Val) {
           either { queue := queue \o <<v>> ;
                    rV := "okay" }
               or { queue := <<v>> \o  queue ;
                    rV := "okay"} 
               or rV := "full" ;
          }
      or { if (queue # << >>)
             { either { rV := Head(queue) ;
                        queue := Tail(queue) }
                   or { rV := queue[Len(queue)] ;
                        queue := [ i \in 1 .. (Len(queue) - 1) |-> queue[i]]}
             }
           else { rV := "empty" } 
         } ;
L2:   rV := null 
    } } }
*)

\* BEGIN TRANSLATION PC-51c7b3db096c8a2759201260936705be386063f4760b0e0dfd43ae4cbdefb4c6
VARIABLES queue, pc, rV

vars == << queue, pc, rV >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ queue = << >>
        (* Process P *)
        /\ rV = [self \in Procs |-> null]
        /\ pc = [self \in ProcSet |-> "L1"]

L1(self) == /\ pc[self] = "L1"
            /\ \/ /\ \E v \in Val:
                       \/ /\ queue' = queue \o <<v>>
                          /\ rV' = [rV EXCEPT ![self] = "okay"]
                       \/ /\ queue' = <<v>> \o  queue
                          /\ rV' = [rV EXCEPT ![self] = "okay"]
                       \/ /\ rV' = [rV EXCEPT ![self] = "full"]
                          /\ queue' = queue
               \/ /\ IF queue # << >>
                        THEN /\ \/ /\ rV' = [rV EXCEPT ![self] = Head(queue)]
                                   /\ queue' = Tail(queue)
                                \/ /\ rV' = [rV EXCEPT ![self] = queue[Len(queue)]]
                                   /\ queue' = [ i \in 1 .. (Len(queue) - 1) |-> queue[i]]
                        ELSE /\ rV' = [rV EXCEPT ![self] = "empty"]
                             /\ queue' = queue
            /\ pc' = [pc EXCEPT ![self] = "L2"]

L2(self) == /\ pc[self] = "L2"
            /\ rV' = [rV EXCEPT ![self] = null]
            /\ pc' = [pc EXCEPT ![self] = "L1"]
            /\ queue' = queue

P(self) == L1(self) \/ L2(self)

Next == (\E self \in Procs: P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(P(self))

\* END TRANSLATION TPC-e8adc767d572c129562b3809f8f8e7c14a330a2e5918786dee3cfc9e499001c3

CONSTANT N

Constraint == Len(queue) \leq N
=============================================================================
