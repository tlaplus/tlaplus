---------------------------- MODULE OneBitMutex ----------------------------
EXTENDS Integers
CONSTANT Procs

(***************************************************************************
--algorithm OneBitMutex
    { 
        variable x = [i \in Procs |-> FALSE];
        fair process (p \in Procs)
            variables unchecked = {};
            other \in Procs ;
            { 
                ncs:- while (TRUE)
                {
                e1: x[self] := TRUE ;
                    unchecked := Procs \ {self};
                e2: while (unchecked # {})
                        {
                        with (i \in unchecked) { other := i } ;
                        unchecked := unchecked \ {other};
                    e3: if (x[other])
                        { 
                            if (TRUE) \* Changed from "self > other" to "TRUE"
                            { 
                            e4: x[self] := FALSE;
                            e5: await ~x[other];
                                goto e1;
                            }
                            else
                            { 
                            e6: await ~x[other];
                            }
                        };
                    } ;
                cs: skip;
                f: x[self] := FALSE
            }
    }
}
 ***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES x, pc, unchecked, other

vars == << x, pc, unchecked, other >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ x = [i \in Procs |-> FALSE]
        (* Process p *)
        /\ unchecked = [self \in Procs |-> {}]
        /\ other \in [Procs -> Procs]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << x, unchecked, other >>

e1(self) == /\ pc[self] = "e1"
            /\ x' = [x EXCEPT ![self] = TRUE]
            /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ other' = other

e2(self) == /\ pc[self] = "e2"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self]:
                            other' = [other EXCEPT ![self] = i]
                       /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {other'[self]}]
                       /\ pc' = [pc EXCEPT ![self] = "e3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED << unchecked, other >>
            /\ x' = x

e3(self) == /\ pc[self] = "e3"
            /\ IF x[other[self]]
                  THEN /\ IF TRUE
                             THEN /\ pc' = [pc EXCEPT ![self] = "e4"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "e6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << x, unchecked, other >>

e4(self) == /\ pc[self] = "e4"
            /\ x' = [x EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "e5"]
            /\ UNCHANGED << unchecked, other >>

e5(self) == /\ pc[self] = "e5"
            /\ ~x[other[self]]
            /\ pc' = [pc EXCEPT ![self] = "e1"]
            /\ UNCHANGED << x, unchecked, other >>

e6(self) == /\ pc[self] = "e6"
            /\ ~x[other[self]]
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << x, unchecked, other >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "f"]
            /\ UNCHANGED << x, unchecked, other >>

f(self) == /\ pc[self] = "f"
           /\ x' = [x EXCEPT ![self] = FALSE]
           /\ pc' = [pc EXCEPT ![self] = "ncs"]
           /\ UNCHANGED << unchecked, other >>

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ e5(self) \/ e6(self) \/ cs(self) \/ f(self)

Next == (\E self \in Procs: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

\* END TRANSLATION

-----------------------------------------------------------------------------
TypeOK == /\ pc \in [{0,1} -> {"r", "e1", "e2", "cs"}]
          /\ x \in [{0,1} -> BOOLEAN]

Past(i,j) == \/ ((pc[i] = "e2") /\ (j \notin unchecked[i]))
             \/ /\ pc[i] \in {"e3", "e6"}
                /\ j \notin unchecked[i] \cup {other[i]}
             \/ pc[i] = "cs"

Inv == /\ TypeOK
       /\ \A i \in Procs :
            /\ (pc[i] \in {"e2", "e3", "e6", "cs"}) => x[i]
            /\ \A j \in Procs \ {i} :
                        Past(i, j) => ~Past(j, i) /\ x[i]


(***************************************************************************
 N-process One-Bit mutual exclusion is _not_ starvation free!
 ***************************************************************************)
StarvationFreedom == \A e \in Procs : pc[e] = "e2" ~> pc[e] = "cs"

 
=============================================================================
