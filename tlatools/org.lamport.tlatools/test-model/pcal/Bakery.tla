------------------------------- MODULE Bakery -------------------------------- 
EXTENDS Naturals, TLC

CONSTANTS NumProcs,     \* The number of processes
          MaxNum        \* For TLC, the maximum value of num[i].

Proc == 1..NumProcs  \* The set of processes

(*   

  --algorithm Bakery
  variable num = [i \in Proc |-> 0] ;
           choosing = [i \in Proc |-> FALSE];
  process proc \in Proc
    variables read = { }; max = 0 ; nxt = self ;
    begin loop : while TRUE
                   do      choosing[self] := TRUE;
                           read := { self };
                           max  := 0 ;
                      d1 : while read # Proc
                            do  with p \in Proc \ read
                                  do if num[p] > max
                                       then max := num[p];
                                     end if ;
                                     read := read \cup {p};
                                end with ;
                            end while ;
                      d2 : num[self] := max + 1 ;
                      d3 : choosing[self] := FALSE ;
                           read := { self } ;
                      w1 : while read # Proc
                            do  with p \in Proc \ read
                                  do     when ~ choosing[p] ;
                                         nxt := p ;
                                end with;
                            w2: when \/ num[nxt] = 0 
                                     \/ num[nxt] > num[self]
                                     \/ /\ num[nxt] = num[self]
                                        /\ nxt > self   ;
                                read := read \cup { nxt } ;
                           end while;
                     cs  : when TRUE ;
                    exit : num[self] := 0;
                  end while;
    end process
  end algorithm


*)
                    
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-3787a86d71fe978e1e68a7e275a515ae
VARIABLES num, choosing, pc, read, max, nxt

vars == << num, choosing, pc, read, max, nxt >>

ProcSet == (Proc)

Init == (* Global variables *)
        /\ num = [i \in Proc |-> 0]
        /\ choosing = [i \in Proc |-> FALSE]
        (* Process proc *)
        /\ read = [self \in Proc |-> { }]
        /\ max = [self \in Proc |-> 0]
        /\ nxt = [self \in Proc |-> self]
        /\ pc = [self \in ProcSet |-> "loop"]

loop(self) == /\ pc[self] = "loop"
              /\ choosing' = [choosing EXCEPT ![self] = TRUE]
              /\ read' = [read EXCEPT ![self] = { self }]
              /\ max' = [max EXCEPT ![self] = 0]
              /\ pc' = [pc EXCEPT ![self] = "d1"]
              /\ UNCHANGED << num, nxt >>

d1(self) == /\ pc[self] = "d1"
            /\ IF read[self] # Proc
                  THEN /\ \E p \in Proc \ read[self]:
                            /\ IF num[p] > max[self]
                                  THEN /\ max' = [max EXCEPT ![self] = num[p]]
                                  ELSE /\ TRUE
                                       /\ max' = max
                            /\ read' = [read EXCEPT ![self] = read[self] \cup {p}]
                       /\ pc' = [pc EXCEPT ![self] = "d1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "d2"]
                       /\ UNCHANGED << read, max >>
            /\ UNCHANGED << num, choosing, nxt >>

d2(self) == /\ pc[self] = "d2"
            /\ num' = [num EXCEPT ![self] = max[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "d3"]
            /\ UNCHANGED << choosing, read, max, nxt >>

d3(self) == /\ pc[self] = "d3"
            /\ choosing' = [choosing EXCEPT ![self] = FALSE]
            /\ read' = [read EXCEPT ![self] = { self }]
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << num, max, nxt >>

w1(self) == /\ pc[self] = "w1"
            /\ IF read[self] # Proc
                  THEN /\ \E p \in Proc \ read[self]:
                            /\ ~ choosing[p]
                            /\ nxt' = [nxt EXCEPT ![self] = p]
                       /\ pc' = [pc EXCEPT ![self] = "w2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ nxt' = nxt
            /\ UNCHANGED << num, choosing, read, max >>

w2(self) == /\ pc[self] = "w2"
            /\ \/ num[nxt[self]] = 0
               \/ num[nxt[self]] > num[self]
               \/ /\ num[nxt[self]] = num[self]
                  /\ nxt[self] > self
            /\ read' = [read EXCEPT ![self] = read[self] \cup { nxt[self] }]
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << num, choosing, max, nxt >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << num, choosing, read, max, nxt >>

exit(self) == /\ pc[self] = "exit"
              /\ num' = [num EXCEPT ![self] = 0]
              /\ pc' = [pc EXCEPT ![self] = "loop"]
              /\ UNCHANGED << choosing, read, max, nxt >>

proc(self) == loop(self) \/ d1(self) \/ d2(self) \/ d3(self) \/ w1(self)
                 \/ w2(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Proc: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-044cd15e6eddcf8edc1cfa67089d17cf

Constraint == \A i \in Proc : num[i] \leq MaxNum

Invariant == \A i, j \in Proc : (pc[i] = "cs") /\ (pc[j] = "cs") => (i = j)
=============================================================================
