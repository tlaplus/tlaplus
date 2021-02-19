----- CONFIG DistBakery ------

CONSTANT
    Nodes <- const_16137059216052000
CONSTRAINT
    constr_16137059216053000
SPECIFICATION
    Spec
INVARIANT
    TypeOK
    Mutex
PROPERTY
    StarvationFree

=============

----------------------------- MODULE DistBakery -----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Nodes
ASSUME Nodes \subseteq Int

MutexProcs == [node : Nodes, type : {"mutex"}] 
MsgProcs   == [node : Nodes, type : {"msg"}]

(***************************************************************************)
(* \ll is the less-than relation for the lexicographical ordering of pairs *)
(* of integers.  It is a total ordering on Int \X Int.                     *)
(***************************************************************************)
pr1 \ll pr2 == \/ pr1[1] < pr2[1]
               \/ /\ pr1[1] = pr2[1]
                  /\ pr1[2] < pr2[2]

(***************************************************************************)
(* For n a node and pr a <<number, node>> pair NextHigher(pr,n) is the     *)
(* smallest integer nm such that pr \ll <<nm, n>>.                         *)
(***************************************************************************)
NextHigher(pr,n) == IF pr[2] < n  THEN pr[1] ELSE pr[1] + 1 

(***************************************************************************)
(* If PrSet is a nonempt set of pairs of integers, then MaxPr(PrSet) is    *)
(* the largest element in PrSet under the \ll ordering.                    *)
(***************************************************************************)
MaxPr(PrSet) == CHOOSE max \in PrSet : \A pr \in PrSet \ {max} : pr \ll max

(***************************************************************************)
(* If num[n1] # 0 and <<num[n1], n1>> \prec <<num[n2], n2>>, then n1 has   *)
(* priority over n2 in entering its critical section.                      *)
(***************************************************************************)
pr1 \prec pr2 == \/ pr2[1] = 0 
                 \/ pr1 \ll pr2

\* messages used in the algorithm
Write(c) == [type |-> "write", num |-> c]
Ack == [type |-> "ack"]

Messages == [type : {"write"}, num : Nat] \cup {Ack}
(*****
--algorithm DistributedMutex {
    variables num  = [n \in Nodes |-> 0] ,
              rnum = [n \in Nodes |-> [m \in Nodes \ {n} |-> 0]],
              acks = [n \in Nodes |-> {}],
              net  = [i \in Nodes |-> [j \in Nodes \ {i} |-> << >>]]             ;
             
   macro Broadcast(msg) {
     net[self.node] := [i \in Nodes \ {self.node} |-> Append(net[self.node][i], msg)]
   } 
   
  macro Rcv(from) {
    net[from][self.node] := Tail(net[from][self.node])
  }
   macro RcvAndReply(from, msg) {
        net[from][self.node] := Tail(net[from][self.node])  
     || net[self.node][from] := Append(net[self.node][from], msg)
   }
     
   fair process(mu \in MutexProcs) {
    ncs:- while (TRUE) {
            skip;  \* non-critical section
   enter:   with (nonZeros = {i \in Nodes \ {self.node} : rnum[self.node][i] # 0},
                  competition = {<<rnum[i], i>> : i \in nonZeros} ) {
              num[self.node] := IF competition = { } 
                                  THEN 1
                                  ELSE NextHigher(MaxPr(competition), self.node) ;
\*              print <<num[self.node], self>>
            } ;
            acks[self.node] := {self.node};
            Broadcast(Write(num[self.node])) ; 
      e1:   await  /\ acks[self.node] = Nodes
                   /\ \A n \in Nodes \ {self.node} : <<num[self.node],self.node>> \prec <<rnum[self.node][n],n>>;
      cs:   skip;
    exit:   \* num[self.node] := num[self.node] + 1;
            Broadcast(Write(0)) ;
          } \* end while
   }


   fair process(mg \in MsgProcs) {
    a: while (TRUE) {
          with (n \in Nodes \ {self.node}) {
             await net[n][self.node] /= << >> ;
             with (msg = Head(net[n][self.node]), 
                   me = self.node) {             
                if (msg.type = "write") {
                    rnum[me][n] := msg.num;
                    if (msg.num = 0) { Rcv(n) }
                    else { RcvAndReply(n, Ack) } ;
                }                                                                   
                else{ acks[me] := acks[me] \cup {n} }
             }  \* end with
           }  \* end with
        }  \* end while
   }
}
***)
\* BEGIN TRANSLATION (chksum(pcal) = "b2c38cfa" /\ chksum(tla) = "56f014e9")
VARIABLES num, rnum, acks, net, pc

vars == << num, rnum, acks, net, pc >>

ProcSet == (MutexProcs) \cup (MsgProcs)

Init == (* Global variables *)
        /\ num = [n \in Nodes |-> 0]
        /\ rnum = [n \in Nodes |-> [m \in Nodes \ {n} |-> 0]]
        /\ acks = [n \in Nodes |-> {}]
        /\ net = [i \in Nodes |-> [j \in Nodes \ {i} |-> << >>]]
        /\ pc = [self \in ProcSet |-> CASE self \in MutexProcs -> "ncs"
                                        [] self \in MsgProcs -> "a"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ UNCHANGED << num, rnum, acks, net >>

enter(self) == /\ pc[self] = "enter"
               /\ LET nonZeros == {i \in Nodes \ {self.node} : rnum[self.node][i] # 0} IN
                    LET competition == {<<rnum[i], i>> : i \in nonZeros} IN
                      num' = [num EXCEPT ![self.node] = IF competition = { }
                                                          THEN 1
                                                          ELSE NextHigher(MaxPr(competition), self.node)]
               /\ acks' = [acks EXCEPT ![self.node] = {self.node}]
               /\ net' = [net EXCEPT ![self.node] = [i \in Nodes \ {self.node} |-> Append(net[self.node][i], (Write(num'[self.node])))]]
               /\ pc' = [pc EXCEPT ![self] = "e1"]
               /\ rnum' = rnum

e1(self) == /\ pc[self] = "e1"
            /\ /\ acks[self.node] = Nodes
               /\ \A n \in Nodes \ {self.node} : <<num[self.node],self.node>> \prec <<rnum[self.node][n],n>>
            /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << num, rnum, acks, net >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << num, rnum, acks, net >>

exit(self) == /\ pc[self] = "exit"
              /\ net' = [net EXCEPT ![self.node] = [i \in Nodes \ {self.node} |-> Append(net[self.node][i], (Write(0)))]]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << num, rnum, acks >>

mu(self) == ncs(self) \/ enter(self) \/ e1(self) \/ cs(self) \/ exit(self)

a(self) == /\ pc[self] = "a"
           /\ \E n \in Nodes \ {self.node}:
                /\ net[n][self.node] /= << >>
                /\ LET msg == Head(net[n][self.node]) IN
                     LET me == self.node IN
                       IF msg.type = "write"
                          THEN /\ rnum' = [rnum EXCEPT ![me][n] = msg.num]
                               /\ IF msg.num = 0
                                     THEN /\ net' = [net EXCEPT ![n][self.node] = Tail(net[n][self.node])]
                                     ELSE /\ net' = [net EXCEPT ![n][self.node] = Tail(net[n][self.node]),
                                                                ![self.node][n] = Append(net[self.node][n], Ack)]
                               /\ acks' = acks
                          ELSE /\ acks' = [acks EXCEPT ![me] = acks[me] \cup {n}]
                               /\ UNCHANGED << rnum, net >>
           /\ pc' = [pc EXCEPT ![self] = "a"]
           /\ num' = num

mg(self) == a(self)

Next == (\E self \in MutexProcs: mu(self))
           \/ (\E self \in MsgProcs: mg(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in MutexProcs : WF_vars((pc[self] # "ncs") /\ mu(self))
        /\ \A self \in MsgProcs : WF_vars(mg(self))

\* END TRANSLATION 
TypeOK == /\ num \in [Nodes -> Nat] 
          /\ /\ (DOMAIN rnum) = Nodes    
             /\ \A n \in Nodes : rnum[n] \in [Nodes \ {n} -> Nat]
          /\ acks \in [Nodes -> SUBSET Nodes]
          /\ /\ (DOMAIN net) = Nodes    
             /\ \A n \in Nodes : net[n] \in [Nodes \ {n} -> Seq(Messages)]

Mutex == \A m, n \in MutexProcs : (n # m) => ~(pc[n] = "cs" /\ pc[m] = "cs")

StarvationFree == \A m \in MutexProcs : (pc[m]="enter") ~> (pc[m]="cs")

------

const_16137059216052000 == 
    {-1, -2}

constr_16137059216053000 ==
    \A n \in Nodes : num[n] =< 4

=============================================================================
\* Modification History
\* Last modified Thu Feb 18 17:54:45 PST 2021 by markus
\* Last modified Thu Feb 18 17:18:09 PST 2021 by lamport
\* Created Thu Feb 18 15:57:59 PST 2021 by lamport
