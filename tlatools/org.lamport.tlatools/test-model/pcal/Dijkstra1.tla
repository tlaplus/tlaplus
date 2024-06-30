--algorithm Dijkstra1
variable M \in [ProcSet -> 0..(K-1)];

  process P0 = 0
    begin
p0: while TRUE do
      when M[0] = M[N-1];
p1:   M[0] := (M[0] + 1) % K;
      end while
    end process;

  process Pi \in 1..(N-1)
    begin
pi: while (TRUE) do
      when M[self] # M[self - 1];
pj:   M[self] := M[self - 1];
      end while
    end process;

  end algorithm

----------- MODULE Dijkstra1 -----------
EXTENDS FiniteSets, Naturals

CONSTANT K, N

ASSUME (K > N) /\ (N > 0) 

\* BEGIN TRANSLATION (chksum(pcal) = "745d7796" /\ chksum(tla) = "72549c2c")
VARIABLES pc, M

vars == << pc, M >>

ProcSet == {0} \cup (1..(N-1))

Init == (* Global variables *)
        /\ M \in [ProcSet -> 0..(K-1)]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "p0"
                                        [] self \in 1..(N-1) -> "pi"]

p0 == /\ pc[0] = "p0"
      /\ M[0] = M[N-1]
      /\ pc' = [pc EXCEPT ![0] = "p1"]
      /\ M' = M

p1 == /\ pc[0] = "p1"
      /\ M' = [M EXCEPT ![0] = (M[0] + 1) % K]
      /\ pc' = [pc EXCEPT ![0] = "p0"]

P0 == p0 \/ p1

pi(self) == /\ pc[self] = "pi"
            /\ M[self] # M[self - 1]
            /\ pc' = [pc EXCEPT ![self] = "pj"]
            /\ M' = M

pj(self) == /\ pc[self] = "pj"
            /\ M' = [M EXCEPT ![self] = M[self - 1]]
            /\ pc' = [pc EXCEPT ![self] = "pi"]

Pi(self) == pi(self) \/ pj(self)

Next == P0
           \/ (\E self \in 1..(N-1): Pi(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(P0)
        /\ \A self \in 1..(N-1) : WF_vars(Pi(self))

\* END TRANSLATION

HasToken(self) == \/ (self = 0) /\ (M[0] = M[N - 1])
                  \/ (self > 0) /\ (M[self] # M[self - 1])

TokenHolders == {self \in ProcSet: HasToken(self)}

SomeoneHoldsToken  == Cardinality(TokenHolders) > 0

EventuallyJustOneHoldsToken == <>[] (Cardinality(TokenHolders) = 1)

THEOREM Spec => [] SomeoneHoldsToken

THEOREM Spec => EventuallyJustOneHoldsToken
========================================
