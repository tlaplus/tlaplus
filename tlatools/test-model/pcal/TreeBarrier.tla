--algorithm TreeBarrier
   variables arrived = [i \in 1..2 |-> [j \in 1..N |-> 0]];
             proceed = [i \in 1..2 |-> [j \in 1..N |-> 0]];
   process i \in 1..N
       variables b = 1;
                 p = 0;
       begin
prc:   while (TRUE) do
comp:     skip;
b1:       if 2*self \leq N then
b2:          when arrived[b][2*self] = 1; arrived[b][2*self] := 0;
b3:          when arrived[b][2*self + 1] = 1; arrived[b][2*self + 1] := 0;
             end if;
b4:       arrived[b][self] := 1;
b5:       if self = 1 then
             p := 1;
b6:          while (p \leq N) do
b7:             proceed[b][p] := 1;
                p := p + 1;
                end while;
             end if;
b8:       when proceed[b][self] = 1; proceed[b][self] := 0;
b9:       b := IF b = 1 THEN 2 ELSE 1;
          end while;
       end process;
end algorithm

------------------------ MODULE TreeBarrier ------------------------

EXTENDS Naturals, Sequences
CONSTANT exp
N == 2^exp-1

--------------------------------------------------------------------

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-f8296f0cc6166098bc809c33e090e03e
VARIABLES arrived, proceed, pc, b, p

vars == << arrived, proceed, pc, b, p >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ arrived = [i \in 1..2 |-> [j \in 1..N |-> 0]]
        /\ proceed = [i \in 1..2 |-> [j \in 1..N |-> 0]]
        (* Process i *)
        /\ b = [self \in 1..N |-> 1]
        /\ p = [self \in 1..N |-> 0]
        /\ pc = [self \in ProcSet |-> "prc"]

prc(self) == /\ pc[self] = "prc"
             /\ pc' = [pc EXCEPT ![self] = "comp"]
             /\ UNCHANGED << arrived, proceed, b, p >>

comp(self) == /\ pc[self] = "comp"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "b1"]
              /\ UNCHANGED << arrived, proceed, b, p >>

b1(self) == /\ pc[self] = "b1"
            /\ IF 2*self \leq N
                  THEN /\ pc' = [pc EXCEPT ![self] = "b2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "b4"]
            /\ UNCHANGED << arrived, proceed, b, p >>

b2(self) == /\ pc[self] = "b2"
            /\ arrived[b[self]][2*self] = 1
            /\ arrived' = [arrived EXCEPT ![b[self]][2*self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "b3"]
            /\ UNCHANGED << proceed, b, p >>

b3(self) == /\ pc[self] = "b3"
            /\ arrived[b[self]][2*self + 1] = 1
            /\ arrived' = [arrived EXCEPT ![b[self]][2*self + 1] = 0]
            /\ pc' = [pc EXCEPT ![self] = "b4"]
            /\ UNCHANGED << proceed, b, p >>

b4(self) == /\ pc[self] = "b4"
            /\ arrived' = [arrived EXCEPT ![b[self]][self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "b5"]
            /\ UNCHANGED << proceed, b, p >>

b5(self) == /\ pc[self] = "b5"
            /\ IF self = 1
                  THEN /\ p' = [p EXCEPT ![self] = 1]
                       /\ pc' = [pc EXCEPT ![self] = "b6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "b8"]
                       /\ p' = p
            /\ UNCHANGED << arrived, proceed, b >>

b6(self) == /\ pc[self] = "b6"
            /\ IF (p[self] \leq N)
                  THEN /\ pc' = [pc EXCEPT ![self] = "b7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "b8"]
            /\ UNCHANGED << arrived, proceed, b, p >>

b7(self) == /\ pc[self] = "b7"
            /\ proceed' = [proceed EXCEPT ![b[self]][p[self]] = 1]
            /\ p' = [p EXCEPT ![self] = p[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "b6"]
            /\ UNCHANGED << arrived, b >>

b8(self) == /\ pc[self] = "b8"
            /\ proceed[b[self]][self] = 1
            /\ proceed' = [proceed EXCEPT ![b[self]][self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "b9"]
            /\ UNCHANGED << arrived, b, p >>

b9(self) == /\ pc[self] = "b9"
            /\ b' = [b EXCEPT ![self] = IF b[self] = 1 THEN 2 ELSE 1]
            /\ pc' = [pc EXCEPT ![self] = "prc"]
            /\ UNCHANGED << arrived, proceed, p >>

i(self) == prc(self) \/ comp(self) \/ b1(self) \/ b2(self) \/ b3(self)
              \/ b4(self) \/ b5(self) \/ b6(self) \/ b7(self) \/ b8(self)
              \/ b9(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..N: i(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-cbb736d8ea82daa6b485e32bbe870840


SafeBarrier == \A p1, p2 \in ProcSet:
   ((pc[p1] = "comp") /\ (pc[p2] = "comp")) => (b[p1] = b[p2])

LiveBarrier == \A p1 \in ProcSet:
                   /\ (b[p1] = 1) ~> (b[p1] = 2)
                   /\ (b[p1] = 2) ~> (b[p1] = 1)

====================================================================
