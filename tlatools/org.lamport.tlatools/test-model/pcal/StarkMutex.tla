--algorithm StarkMutex
  variables flag = [i \in 1..N |-> FALSE]; 
            next = 1;
            empty = TRUE;
            mutex = 1;
            weakSem = [i \in 1..N |-> 0];
  process i \in 1..N
    variables first = FALSE;
              j = 1;
    begin
    in1: while (TRUE) do
         flag[self] := TRUE;
         first := FALSE;
    in2: when mutex = 1; mutex := 0;
    in3: if empty then
    in4:    empty := FALSE;
            first := TRUE;
            end if;
    in5:    mutex := 1;
    in6:    if ~ first then
               when weakSem[self] = 1; weakSem[self] := 0;
             end if;
    cs:     skip;
    ex1:    flag[self] := FALSE;
    ex2:    when mutex = 1; mutex := 0;
    ex3:    j := 1;
            empty := TRUE;
    ex4:    while j \leq N do
               if flag[IF next + j > N THEN next + j - N ELSE next + j] then
    ex5:          with n = IF next + j > N THEN next + j - N ELSE next + j do
                     next := n;
                     weakSem[n] := 1;
                     j := N + 1;
                     end with;
    ex6:          empty := FALSE;
               else
    ex7:          j := j + 1;
               end if;
            end while;
    ex8:    mutex := 1;
    nc:     skip;
            end while;
    end process
  end algorithm



------------------ MODULE StarkMutex ------------------

EXTENDS Naturals, Sequences
CONSTANT N

-------------------------------------------------------



\* BEGIN TRANSLATION
VARIABLES flag, next, empty, mutex, weakSem, pc, first, j

vars == << flag, next, empty, mutex, weakSem, pc, first, j >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ flag = [i \in 1..N |-> FALSE]
        /\ next = 1
        /\ empty = TRUE
        /\ mutex = 1
        /\ weakSem = [i \in 1..N |-> 0]
        (* Process i *)
        /\ first = [self \in 1..N |-> FALSE]
        /\ j = [self \in 1..N |-> 1]
        /\ pc = [self \in ProcSet |-> "in1"]

in1(self) == /\ pc[self] = "in1"
             /\ flag' = [flag EXCEPT ![self] = TRUE]
             /\ first' = [first EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "in2"]
             /\ UNCHANGED << next, empty, mutex, weakSem, j >>

in2(self) == /\ pc[self] = "in2"
             /\ mutex = 1
             /\ mutex' = 0
             /\ pc' = [pc EXCEPT ![self] = "in3"]
             /\ UNCHANGED << flag, next, empty, weakSem, first, j >>

in3(self) == /\ pc[self] = "in3"
             /\ IF empty
                   THEN /\ pc' = [pc EXCEPT ![self] = "in4"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "in5"]
             /\ UNCHANGED << flag, next, empty, mutex, weakSem, first, j >>

in4(self) == /\ pc[self] = "in4"
             /\ empty' = FALSE
             /\ first' = [first EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "in5"]
             /\ UNCHANGED << flag, next, mutex, weakSem, j >>

in5(self) == /\ pc[self] = "in5"
             /\ mutex' = 1
             /\ pc' = [pc EXCEPT ![self] = "in6"]
             /\ UNCHANGED << flag, next, empty, weakSem, first, j >>

in6(self) == /\ pc[self] = "in6"
             /\ IF ~ first[self]
                   THEN /\ weakSem[self] = 1
                        /\ weakSem' = [weakSem EXCEPT ![self] = 0]
                   ELSE /\ TRUE
                        /\ UNCHANGED weakSem
             /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << flag, next, empty, mutex, first, j >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "ex1"]
            /\ UNCHANGED << flag, next, empty, mutex, weakSem, first, j >>

ex1(self) == /\ pc[self] = "ex1"
             /\ flag' = [flag EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ex2"]
             /\ UNCHANGED << next, empty, mutex, weakSem, first, j >>

ex2(self) == /\ pc[self] = "ex2"
             /\ mutex = 1
             /\ mutex' = 0
             /\ pc' = [pc EXCEPT ![self] = "ex3"]
             /\ UNCHANGED << flag, next, empty, weakSem, first, j >>

ex3(self) == /\ pc[self] = "ex3"
             /\ j' = [j EXCEPT ![self] = 1]
             /\ empty' = TRUE
             /\ pc' = [pc EXCEPT ![self] = "ex4"]
             /\ UNCHANGED << flag, next, mutex, weakSem, first >>

ex4(self) == /\ pc[self] = "ex4"
             /\ IF j[self] \leq N
                   THEN /\ IF flag[IF next + j[self] > N THEN next + j[self] - N ELSE next + j[self]]
                              THEN /\ pc' = [pc EXCEPT ![self] = "ex5"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "ex7"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "ex8"]
             /\ UNCHANGED << flag, next, empty, mutex, weakSem, first, j >>

ex5(self) == /\ pc[self] = "ex5"
             /\ LET n == IF next + j[self] > N THEN next + j[self] - N ELSE next + j[self] IN
                  /\ next' = n
                  /\ weakSem' = [weakSem EXCEPT ![n] = 1]
                  /\ j' = [j EXCEPT ![self] = N + 1]
             /\ pc' = [pc EXCEPT ![self] = "ex6"]
             /\ UNCHANGED << flag, empty, mutex, first >>

ex6(self) == /\ pc[self] = "ex6"
             /\ empty' = FALSE
             /\ pc' = [pc EXCEPT ![self] = "ex4"]
             /\ UNCHANGED << flag, next, mutex, weakSem, first, j >>

ex7(self) == /\ pc[self] = "ex7"
             /\ j' = [j EXCEPT ![self] = j[self] + 1]
             /\ pc' = [pc EXCEPT ![self] = "ex4"]
             /\ UNCHANGED << flag, next, empty, mutex, weakSem, first >>

ex8(self) == /\ pc[self] = "ex8"
             /\ mutex' = 1
             /\ pc' = [pc EXCEPT ![self] = "nc"]
             /\ UNCHANGED << flag, next, empty, weakSem, first, j >>

nc(self) == /\ pc[self] = "nc"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "in1"]
            /\ UNCHANGED << flag, next, empty, mutex, weakSem, first, j >>

i(self) == in1(self) \/ in2(self) \/ in3(self) \/ in4(self) \/ in5(self)
              \/ in6(self) \/ cs(self) \/ ex1(self) \/ ex2(self)
              \/ ex3(self) \/ ex4(self) \/ ex5(self) \/ ex6(self)
              \/ ex7(self) \/ ex8(self) \/ nc(self)

Next == (\E self \in 1..N: i(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

StarkSpec == /\ Spec
             /\ \A self \in ProcSet:
                /\ WF_vars(in1(self))
                /\ WF_vars(in2(self))
                /\ WF_vars(in3(self))
                /\ WF_vars(in4(self))
                /\ WF_vars(in5(self))
                /\ WF_vars(in6(self))
                /\ WF_vars(ex1(self))
                /\ WF_vars(ex2(self))
                /\ WF_vars(ex3(self))
                /\ WF_vars(ex4(self))
                /\ WF_vars(ex5(self))
                /\ WF_vars(ex6(self))
                /\ WF_vars(ex7(self))
                /\ WF_vars(ex8(self))
                /\ WF_vars(cs(self))

Mutex == \A p1, p2 \in ProcSet: (pc[p1] = "cs" /\ pc[p2] = "pc") => (p1 = p2)

StarvationFree == \A p \in ProcSet: pc[p] = "in1" ~> pc[p] = "cs"
=======================================================

