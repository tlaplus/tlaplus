---- CONFIG DistBakery3aAuxMC ----
\* CONSTANT declarations
CONSTANT AnyNum = AnyNum
\* CONSTANT definitions
CONSTANT
Nodes <- const_1616950483165138000
\* CONSTANT definitions
CONSTANT
EdgeIdToEdge <- const_1616950483165139000
\* CONSTANT definitions
CONSTANT
EdgeIds <- const_1616950483165140000
\* CONSTANT definition
CONSTANT
Nat <- def_ov_1616950483165141000
\* CONSTRAINT definition
CONSTRAINT
constr_1616950483165142000
\* SPECIFICATION definition
SPECIFICATION
FSpec
\* INVARIANT definition
INVARIANT
TypeOK
Mutex
TypeOKBar
\* PROPERTY definition
PROPERTY
StarvationFree
====

---- MODULE DistBakery3aAuxMC ----
EXTENDS DistBakery3aAux, TLC

\* CONSTANT definitions @modelParameterConstants:0Nodes
const_1616950483165138000 ==
{-1, -2}
----

\* CONSTANT definitions @modelParameterConstants:2EdgeIdToEdge(eid)
const_1616950483165139000(eid) ==
TestEdgeIdToEdge(eid)
----

\* CONSTANT definitions @modelParameterConstants:3EdgeIds
const_1616950483165140000 ==
TestEdgeIds
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1616950483165141000 ==
TestNat
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1616950483165142000 ==
\A n \in Nodes : num[n] =< TestMaxNum
----
=============================================================================

-------------------------- MODULE DistBakery3aAux --------------------------

(***************************************************************************)
(* This is the distributed bakery algorithm that I hope implements         *)
(* DistBakery2a.  It is a modification of DistBakery in                    *)
(* ~/tla/web/tutorial/trial-specs/, differing in allowing aribtrarily      *)
(* large values of num[i] to be chosen in the enter step, not just the     *)
(* smallest possible value.  This is hell for model checking, but makes    *)
(* for a simpler spec.                                                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC
                     
CONSTANT Nodes, EdgeIds, EdgeIdToEdge(_)

Edges == {e \in Nodes \X Nodes : e[1] # e[2]}


ASSUME NodesAssump ==  Nodes \subseteq Int
ASSUME NodesFinite == IsFiniteSet(Nodes)

N == Cardinality(Nodes)

ASSUME EdgeIdsAssump == 
         /\ \A w \in EdgeIds : EdgeIdToEdge(w) \in Edges
         /\ \A n \in Edges : \E w \in EdgeIds : EdgeIdToEdge(w) = n

Src(eid)  == EdgeIdToEdge(eid)[1]
Dest(eid) == EdgeIdToEdge(eid)[2]


(***************************************************************************)
(* \ll is the less-than relation for the lexicographical ordering of pairs *)
(* of integers.  It is a total ordering on Int \X Int.                     *)
(***************************************************************************)
pr1 \ll pr2 == \/ pr1[1] < pr2[1]
               \/ /\ pr1[1] = pr2[1]
                  /\ pr1[2] < pr2[2]

(***************************************************************************)
(* If S is a set of numbers, then Sequentialize(S) is the sequence of      *)
(* elements of S in increasing numerical order.                            *)
(***************************************************************************)
RECURSIVE Sequentialize(_) 
Sequentialize(S) == 
  LET SetMax(T) == CHOOSE t \in T : \A r \in T : t >= r
  IN  IF S = {} THEN << >> 
                ELSE Append(Sequentialize(S \ {SetMax(S)}), SetMax(S))
                   

Procs == Nodes
SubProcs == {q \in Nodes \X Nodes : q[1] # q[2]}
subProcsOf(pid) == {q \in SubProcs : q[1] = pid[1]}
ProcIds == {<<p>> : p \in Nodes}
Mirror(q) == <<q[2], q[1]>>
Wr0Procs == {<<q[1], q[2], "wr0">> : q \in SubProcs}
ProcSetBar == SubProcs \cup ProcIds \cup Wr0Procs

(***************************************************************************)
(* The function with domain S that maps every element in S to 0.           *)
(***************************************************************************)
Zeros(S) == [i \in S |-> 0]

(***************************************************************************)
(* The function with domain S that maps every element in S to v.           *)
(***************************************************************************)
ArrayOf(S,v) == [i \in S |-> v]


(***************************************************************************)
(* For a function fcn with S a subset of its domain, this is the function  *)
(* obtained from fcn by executing  f[x] := val  for all x in S.            *)
(***************************************************************************)                                            
Replace(fcn, S, val) ==
  [x \in DOMAIN fcn |-> IF x \in S THEN val ELSE fcn[x]]  

CONSTANT AnyNum
ASSUME AnyNum \notin Nat
                  

\*(***************************************************************************)
\*(* For n a node and pr a <<number, node>> pair NextHigher(pr,n) is the     *)
\*(* smallest integer nm such that pr \ll <<nm, n>>.                         *)
\*(***************************************************************************)
\*NextHigher(pr,n) == IF pr[2] < n  THEN pr[1] ELSE pr[1] + 1 
\*
\*(***************************************************************************)
\*(* If PrSet is a nonempt set of pairs of integers, then MaxPr(PrSet) is    *)
\*(* the largest element in PrSet under the \ll ordering.                    *)
\*(***************************************************************************)
\*MaxPr(PrSet) == CHOOSE max \in PrSet : \A pr \in PrSet \ {max} : pr \ll max
\*
\*(***************************************************************************)
\*(* If num[n1] # 0 and <<num[n1], n1>> \prec <<num[n2], n2>>, then n1 has   *)
\*(* priority over n2 in entering its critical section.                      *)
\*(***************************************************************************)
\*pr1 \prec pr2 == \/ pr2[1] = 0 
\*                 \/ pr1 \ll pr2


\* messages used in the algorithm
Write(c) == [type |-> "write", num |-> c]
Ack == [type |-> "ack"]

Messages == [type : {"write"}, num : Nat] \cup {Ack}


(***********
--algorithm DBakery3a {
    variables num  = [n \in Nodes |-> 0] ,
              rnum = [n \in Nodes |-> [m \in Nodes |-> 0]],
              acks = [n \in Nodes |-> {}],
              net  = [i \in Nodes |-> [k \in Nodes  |-> << >>]] ,
              numBar = Zeros(Procs) ,
              tempBar = Zeros(SubProcs) ,
              mustRdBar = ArrayOf(SubProcs, TRUE) ,
              pcBar = [self \in ProcSetBar |->
                          CASE self \in SubProcs -> "M1s"
                            [] self \in ProcIds -> "ncs"
                            [] self \in Wr0Procs -> "wr0"] ,
\*              rnumH  = rnum ;
                \* A history variable to capture the state of rnum[n] when an
                \* enter(n) step is executed.
              msgStop = [n \in Nodes |-> FALSE] ;
                \* A suttering variable that prevents any messages from being
                \* being received while msgStop[n] equals TRUE for some n .
             
   macro Broadcast(msg) {
     net[self] := [i \in Nodes |-> 
                         IF i = self THEN << >>
                                     ELSE Append(net[self][i], msg)]
   } 
   
 macro Rcv(from) {
    net[from][Dest(self)] := Tail(net[from][Dest(self)])
  }
  
  macro RcvAndReply(from, msg) {
        net[from][Dest(self)] := Tail(net[from][Dest(self)])  
     || net[Dest(self)][from] := Append(net[Dest(self)][from], msg)
   }
     
   fair process(mu \in Nodes) 
     variable j = 1 ; { \***************************************************************
    \* pcBar[<<self, *>>] = "enter"
    ncs:- while (TRUE) {
            skip;  \* non-critical section
            pcBar[<<self>>] := "L1" ;
            (***************************************************************)
            (* L1(self) is a stuttering step that implements L1(<<self>>). *)
            (***************************************************************)
      L1:   mustRdBar := Replace(mustRdBar, 
                          {Mirror(p) : p \in subProcsOf(<<self>>)}, FALSE) ;  \******************
            pcBar[<<self>>] := "M1" ;  \********************************************
    (***********************************************************************)
    (* M1s(self) performs stuttering steps immediately preceding an        *)
    (* enter(self) step that simulates all the M1s(<<self,*>>) actions of  *)
    (* ProtoBakery.                                                        *)
    (***********************************************************************)
    M1s:   while (j < N) {      
               msgStop[self] := TRUE ;                         \***********
               with (n = Sequentialize(Nodes \ {self})[j]) {   \***********
                 tempBar[<<self, n>>] := rnum[self][n] ;         \***********
                 pcBar[<<self, n>>] := "L2" ;                  \***********
                 j := j+1                                       \***********
               } ;                                              \***********
             } ;                                                \***********
             j := 1 ;                                           \***********

            (***************************************************************)
            (* enter(self) simulates the M1(<<self>>) action of            *)
            (* ProtoBakery.                                                *)
            (***************************************************************)
   enter:   with (nonZeros = {i \in Nodes \ {self} : rnum[self][i] # 0},
                  competitors = {<<rnum[self][i], i>> : i \in nonZeros},
                  newnum \in {i \in Nat \ {0}  : \A c \in competitors:
                                                         c \ll <<i, self>>}
                   ) {
              num[self] := newnum ;                                
              acks[self] := {};
              Broadcast(Write(num[self])) ; 
              pcBar[<<self>>] := "pcs" ;   \*****************************************
              numBar[self] := newnum ;    \*****************************************
              tempBar := Replace(tempBar, subProcsOf(<<self>>), 0) ;  \*************
              mustRdBar := Replace(mustRdBar, 
                          {Mirror(p) : p \in subProcsOf(<<self>>)}, FALSE) ;  \****************** 
\*              rnumH[self] := rnum[self] ; \*****************************************
              msgStop[self] := FALSE  \**********
            } ;
    
            (***************************************************************)
            (* wait(s) simulates a stuttering action of ProtoBakery.       *)
            (***************************************************************)
    wait:   await  \A n \in Nodes \ {self} :
                     /\ n \in acks[self] 
                     /\ \/ rnum[self][n] = 0
                        \/ <<num[self],self>> \ll <<rnum[self][n],n>>;
            msgStop[self] := TRUE ; \**********
    (***********************************************************************)
    (* The ProtoBakery's L2(<<self, *>>) and L3(<<self,*>>) are            *)
    (* implemented by the following L2(self) and L3(self) steps.  The last *)
    (* L3(self) step implements the pcs(<<self>>) step.                    *)
    (*                                                                     *)
    (* Since neither of these statements wait and they do not affect any   *)
    (* variables of the DistBakery algorithm except pc, they essentially   *)
    (* do not modify the algorithm.  They are stuttering steps if we       *)
    (* consider pc to be a hidden (existentially quantified) variable of   *)
    (* the DistBakery spec.                                                *)
    (***********************************************************************)
       L2:  while (j < N) {   \*********************************************
               with (m = Sequentialize(Nodes \ {self})[j]) {  \****************
                 pcBar[<<self, m>>] :=  "L3"          \****************
               } ;                                         \****************
             j := j+1;                                      \****************
             } ;                                           \****************
             j := 1 ;                                      \****************                                         \***********
    
       L3:  while (j < N) {   \*********************************************
               with (m = Sequentialize(Nodes \ {self})[j]) {  \****************
                pcBar[<<self,m>>] :=  "scs"                  \****************
                } ;                                          \****************
             j := j+1;                                       \****************
             } ;                                             \****************
             j := 1 ;                                        \****************
             pcBar[<<self>>] := "cs" ;
             msgStop[self] := FALSE ;                        \**************** 

            (***************************************************************)
            (* cs(self) implements cs(<<self>>).                           *)
            (***************************************************************)
      cs:   skip;
            numBar[self] := 0 ;
            mustRdBar := Replace(mustRdBar, subProcsOf(<<self>>), FALSE) ;
            pcBar[<<self>>] := "ncs";
            
            (***************************************************************)
            (* exit(self) simulates a stuttering step of ProtoBakery.      *)
            (***************************************************************)
    exit:   acks[self] := { } ; \* to reduce the state space a bit
            num[self] := 0 ; \* to reduce the state space a bit
            Broadcast(Write(0)) ;
\*            msgStop[self] := TRUE ;
            (***************************************************************)
            (* The following statement executes the scs(<<self,*>>) steps  *)
            (* of ProtoBakery.                                             *)
            (***************************************************************)
     scs:   while (j < N) {   \*********************************************
               with (m = Sequentialize(Nodes \ {self})[j]) {  \****************
                pcBar[<<self,m>>] :=  "M1s"                  \****************
                } ;                                          \****************
             j := j+1;                                       \****************
             } ;                                             \****************
             j := 1 ;                                        \****************
\*             msgStop[self] := FALSE;                         \****************
          } \* end while
   }


  fair process(mg \in EdgeIds) {
    a:- while (TRUE) {
          await ~ \E n \in Nodes : msgStop[n] ;  \********************************
          with (n =  Dest(self), m = Src(self)) {
             await net[m][n] /= << >> ;
             with (msg = Head(net[m][n])) {             
                if (msg.type = "write") {
                    rnum[n][m] := msg.num;
                    if (msg.num = 0) { 
                       Rcv(m);
                       if (pcBar[<<m>>] \in {"ncs", "L1"}) {
                          mustRdBar[<<n,m>>] := TRUE } }
                    else { RcvAndReply(m, Ack) } ;
                }                                                                   
                else{ 
                  Rcv(m) ;
                  acks[n] := acks[n] \cup {m} 
                }                
             }  \* end with
           }  \* end with
        }  \* end while
   }
}
*********************)
\* BEGIN TRANSLATION (chksum(pcal) = "e2175d78" /\ chksum(tla) = "3a13e6d7")
VARIABLES num, rnum, acks, net, numBar, tempBar, mustRdBar, pcBar, msgStop, 
          pc, j

vars == << num, rnum, acks, net, numBar, tempBar, mustRdBar, pcBar, msgStop, 
           pc, j >>

ProcSet == (Nodes) \cup (EdgeIds)

Init == (* Global variables *)
        /\ num = [n \in Nodes |-> 0]
        /\ rnum = [n \in Nodes |-> [m \in Nodes |-> 0]]
        /\ acks = [n \in Nodes |-> {}]
        /\ net = [i \in Nodes |-> [k \in Nodes  |-> << >>]]
        /\ numBar = Zeros(Procs)
        /\ tempBar = Zeros(SubProcs)
        /\ mustRdBar = ArrayOf(SubProcs, TRUE)
        /\ pcBar = [self \in ProcSetBar |->
                       CASE self \in SubProcs -> "M1s"
                         [] self \in ProcIds -> "ncs"
                         [] self \in Wr0Procs -> "wr0"]
        /\ msgStop = [n \in Nodes |-> FALSE]
        (* Process mu *)
        /\ j = [self \in Nodes |-> 1]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> "ncs"
                                        [] self \in EdgeIds -> "a"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pcBar' = [pcBar EXCEPT ![<<self>>] = "L1"]
             /\ pc' = [pc EXCEPT ![self] = "L1"]
             /\ UNCHANGED << num, rnum, acks, net, numBar, tempBar, mustRdBar, 
                             msgStop, j >>

L1(self) == /\ pc[self] = "L1"
            /\ mustRdBar' = Replace(mustRdBar,
                             {Mirror(p) : p \in subProcsOf(<<self>>)}, FALSE)
            /\ pcBar' = [pcBar EXCEPT ![<<self>>] = "M1"]
            /\ pc' = [pc EXCEPT ![self] = "M1s"]
            /\ UNCHANGED << num, rnum, acks, net, numBar, tempBar, msgStop, j >>

M1s(self) == /\ pc[self] = "M1s"
             /\ IF j[self] < N
                   THEN /\ msgStop' = [msgStop EXCEPT ![self] = TRUE]
                        /\ LET n == Sequentialize(Nodes \ {self})[j[self]] IN
                             /\ tempBar' = [tempBar EXCEPT ![<<self, n>>] = rnum[self][n]]
                             /\ pcBar' = [pcBar EXCEPT ![<<self, n>>] = "L2"]
                             /\ j' = [j EXCEPT ![self] = j[self]+1]
                        /\ pc' = [pc EXCEPT ![self] = "M1s"]
                   ELSE /\ j' = [j EXCEPT ![self] = 1]
                        /\ pc' = [pc EXCEPT ![self] = "enter"]
                        /\ UNCHANGED << tempBar, pcBar, msgStop >>
             /\ UNCHANGED << num, rnum, acks, net, numBar, mustRdBar >>

enter(self) == /\ pc[self] = "enter"
               /\ LET nonZeros == {i \in Nodes \ {self} : rnum[self][i] # 0} IN
                    LET competitors == {<<rnum[self][i], i>> : i \in nonZeros} IN
                      \E newnum \in {i \in Nat \ {0}  : \A c \in competitors:
                                                                c \ll <<i, self>>}:
                        /\ num' = [num EXCEPT ![self] = newnum]
                        /\ acks' = [acks EXCEPT ![self] = {}]
                        /\ net' = [net EXCEPT ![self] = [i \in Nodes |->
                                                               IF i = self THEN << >>
                                                                           ELSE Append(net[self][i], (Write(num'[self])))]]
                        /\ pcBar' = [pcBar EXCEPT ![<<self>>] = "pcs"]
                        /\ numBar' = [numBar EXCEPT ![self] = newnum]
                        /\ tempBar' = Replace(tempBar, subProcsOf(<<self>>), 0)
                        /\ mustRdBar' =  Replace(mustRdBar,
                                        {Mirror(p) : p \in subProcsOf(<<self>>)}, FALSE)
                        /\ msgStop' = [msgStop EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "wait"]
               /\ UNCHANGED << rnum, j >>

wait(self) == /\ pc[self] = "wait"
              /\ \A n \in Nodes \ {self} :
                   /\ n \in acks[self]
                   /\ \/ rnum[self][n] = 0
                      \/ <<num[self],self>> \ll <<rnum[self][n],n>>
              /\ msgStop' = [msgStop EXCEPT ![self] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "L2"]
              /\ UNCHANGED << num, rnum, acks, net, numBar, tempBar, mustRdBar, 
                              pcBar, j >>

L2(self) == /\ pc[self] = "L2"
            /\ IF j[self] < N
                  THEN /\ LET m == Sequentialize(Nodes \ {self})[j[self]] IN
                            pcBar' = [pcBar EXCEPT ![<<self, m>>] = "L3"]
                       /\ j' = [j EXCEPT ![self] = j[self]+1]
                       /\ pc' = [pc EXCEPT ![self] = "L2"]
                  ELSE /\ j' = [j EXCEPT ![self] = 1]
                       /\ pc' = [pc EXCEPT ![self] = "L3"]
                       /\ pcBar' = pcBar
            /\ UNCHANGED << num, rnum, acks, net, numBar, tempBar, mustRdBar, 
                            msgStop >>

L3(self) == /\ pc[self] = "L3"
            /\ IF j[self] < N
                  THEN /\ LET m == Sequentialize(Nodes \ {self})[j[self]] IN
                            pcBar' = [pcBar EXCEPT ![<<self,m>>] = "scs"]
                       /\ j' = [j EXCEPT ![self] = j[self]+1]
                       /\ pc' = [pc EXCEPT ![self] = "L3"]
                       /\ UNCHANGED msgStop
                  ELSE /\ j' = [j EXCEPT ![self] = 1]
                       /\ pcBar' = [pcBar EXCEPT ![<<self>>] = "cs"]
                       /\ msgStop' = [msgStop EXCEPT ![self] = FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << num, rnum, acks, net, numBar, tempBar, mustRdBar >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ numBar' = [numBar EXCEPT ![self] = 0]
            /\ mustRdBar' = Replace(mustRdBar, subProcsOf(<<self>>), FALSE)
            /\ pcBar' = [pcBar EXCEPT ![<<self>>] = "ncs"]
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << num, rnum, acks, net, tempBar, msgStop, j >>

exit(self) == /\ pc[self] = "exit"
              /\ acks' = [acks EXCEPT ![self] = { }]
              /\ num' = [num EXCEPT ![self] = 0]
              /\ net' = [net EXCEPT ![self] = [i \in Nodes |->
                                                     IF i = self THEN << >>
                                                                 ELSE Append(net[self][i], (Write(0)))]]
              /\ pc' = [pc EXCEPT ![self] = "scs"]
              /\ UNCHANGED << rnum, numBar, tempBar, mustRdBar, pcBar, msgStop, 
                              j >>

scs(self) == /\ pc[self] = "scs"
             /\ IF j[self] < N
                   THEN /\ LET m == Sequentialize(Nodes \ {self})[j[self]] IN
                             pcBar' = [pcBar EXCEPT ![<<self,m>>] = "M1s"]
                        /\ j' = [j EXCEPT ![self] = j[self]+1]
                        /\ pc' = [pc EXCEPT ![self] = "scs"]
                   ELSE /\ j' = [j EXCEPT ![self] = 1]
                        /\ pc' = [pc EXCEPT ![self] = "ncs"]
                        /\ pcBar' = pcBar
             /\ UNCHANGED << num, rnum, acks, net, numBar, tempBar, mustRdBar, 
                             msgStop >>

mu(self) == ncs(self) \/ L1(self) \/ M1s(self) \/ enter(self) \/ wait(self)
               \/ L2(self) \/ L3(self) \/ cs(self) \/ exit(self)
               \/ scs(self)

a(self) == /\ pc[self] = "a"
           /\ ~ \E n \in Nodes : msgStop[n]
           /\ LET n == Dest(self) IN
                LET m == Src(self) IN
                  /\ net[m][n] /= << >>
                  /\ LET msg == Head(net[m][n]) IN
                       IF msg.type = "write"
                          THEN /\ rnum' = [rnum EXCEPT ![n][m] = msg.num]
                               /\ IF msg.num = 0
                                     THEN /\ net' = [net EXCEPT ![m][Dest(self)] = Tail(net[m][Dest(self)])]
                                          /\ IF pcBar[<<m>>] \in {"ncs", "L1"}
                                                THEN /\ mustRdBar' = [mustRdBar EXCEPT ![<<n,m>>] = TRUE]
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED mustRdBar
                                     ELSE /\ net' = [net EXCEPT ![m][Dest(self)] = Tail(net[m][Dest(self)]),
                                                                ![Dest(self)][m] = Append(net[Dest(self)][m], Ack)]
                                          /\ UNCHANGED mustRdBar
                               /\ acks' = acks
                          ELSE /\ net' = [net EXCEPT ![m][Dest(self)] = Tail(net[m][Dest(self)])]
                               /\ acks' = [acks EXCEPT ![n] = acks[n] \cup {m}]
                               /\ UNCHANGED << rnum, mustRdBar >>
           /\ pc' = [pc EXCEPT ![self] = "a"]
           /\ UNCHANGED << num, numBar, tempBar, pcBar, msgStop, j >>

mg(self) == a(self)

Next == (\E self \in Nodes: mu(self))
           \/ (\E self \in EdgeIds: mg(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars((pc[self] # "ncs") /\ mu(self))
        /\ \A self \in EdgeIds : WF_vars((pc[self] # "a") /\ mg(self))

\* END TRANSLATION 
-----------------------------------------------------------------------------
a1(self) == /\ pc[self] = "a"
           /\ LET n == Dest(self) IN
                LET m == Src(self) IN
                  /\ net[m][n] /= << >>
                  /\ LET msg == Head(net[m][n]) IN
                       IF msg.type = "write"
                          THEN /\ rnum' = [rnum EXCEPT ![n][m] = msg.num]
                               /\ IF msg.num = 0
                                     THEN /\ net' = [net EXCEPT ![m][Dest(self)] = Tail(net[m][Dest(self)])]
                                          /\ IF pcBar[m] \in {"ncs", "L1"}
                                                THEN /\ mustRdBar' = [mustRdBar EXCEPT ![<<n,m>>] = TRUE]
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED mustRdBar
                                     ELSE /\ net' = [net EXCEPT ![m][Dest(self)] = Tail(net[m][Dest(self)]),
                                                                ![Dest(self)][m] = Append(net[Dest(self)][m], Ack)]
                                          /\ UNCHANGED mustRdBar
                               /\ acks' = acks
                          ELSE /\ net' = [net EXCEPT ![m][Dest(self)] = Tail(net[m][Dest(self)])]
                               /\ acks' = [acks EXCEPT ![n] = acks[n] \cup {m}]
                               /\ UNCHANGED << rnum, mustRdBar >>
           /\ pc' = [pc EXCEPT ![self] = "a"]
           /\ UNCHANGED << num, numBar, tempBar, pcBar, msgStop, j >>
            
FSpec == Spec /\ \A self \in EdgeIds : WF_vars(a1(self))
-----------------------------------------------------------------------------

TypeOK == /\ num \in [Nodes -> Nat]
          /\ rnum \in {f \in [Nodes -> [Nodes -> Nat]] :
                            \A n \in Nodes : f[n][n] = 0}
          /\ acks \in [Nodes -> SUBSET Nodes]
          /\ /\ net \in {f \in [Nodes -> [Nodes -> Seq(Messages)]] :
                               \A n \in Nodes : net[n][n] = << >> }
             /\ \A n, m \in Nodes : 
                  \A i, k \in 1..Len(net[n][m]) :
                     /\ (i < k) 
                     /\  net[n][m][i].type = "write" 
                     /\ net[n][m][k].type = "write"
                     => /\ net[n][m][i].num = 0   
                        /\ net[n][m][k].num > 0
          /\ /\ pc \in [Nodes \cup EdgeIds -> STRING]
             /\ \A n \in Nodes : pc[n] \in {"ncs", "L1", "M1s", "enter", "wait", 
                                             "L2", "L3", "cs", "exit", "scs"}
             /\ \A n \in EdgeIds : pc[n] = "a"

TypeOKBar == /\ numBar  \in [Procs -> Nat]
             /\ mustRdBar \in [SubProcs -> BOOLEAN]
             /\ tempBar \in [SubProcs -> Nat]  
             /\ pcBar \in [ProcSetBar -> STRING]

Mutex == \A m, n \in Nodes : (n # m) => ~(pc[n] = "cs" /\ pc[m] = "cs")

StarvationFree == \A m \in Nodes : (pc[m]="enter") ~> (pc[m]="cs")
-----------------------------------------------------------------------------

PB == INSTANCE ProtoBakeryTest
      WITH num <- numBar, mustRd <- mustRdBar, temp <-tempBar, pc <- pcBar

-----------------------------------------------------------------------------
(***************************************************************************
GARBAGE IS BELOW HERE.
 ***************************************************************************)






(***************************************************************************)
(* HasWriteOf(n,m,val) equals TRUE iff there is a "write" message with     *)
(* value val in transit from m to n.                                       *)
(*                                                                         *)
(* HasAck(n,m) equals TRUE iff there is an "ack" message in transit from n *)
(* to m.                                                                   *)
(***************************************************************************)
HasWriteOf(n,m,val) == \E i \in 1..Len(net[n][m]) : /\ net[n][m][i].type = "write"
                                                    /\ net[n][m][i].num = val
HasAck(n,m) == \E i \in 1..Len(net[n][m]) : net[n][m][i].type = "ack"

Inv == \A n \in Nodes : \A m \in Nodes \ {n} :
         /\ pc[n] \in {"wait", "cs"} => 
              /\ num[n] > 0
              /\ \/ /\ m \notin acks[n]
                    /\ \/ HasWriteOf(n,m,num[n])
                       \/ /\ HasAck(m,n)
                          /\ rnum[m][n] = num[n]                              
                 \/ /\ m \in acks[n]
                    /\ rnum[m][n] = num[n]
         /\ /\ pc[n] = "wait" 
            /\ pc[m] \in {"wait", "cs"} 
            /\ m \in acks[n]
            => \/ rnum[n][m] = num[m]
               \/ <<num[n], n>> \ll <<num[m], m>>
         /\ (pc[n] = "cs") /\ (pc[m] \in {"wait", "cs"})
               => <<num[n], n>> \ll <<num[m], m>>

Inv1 == \A n \in Nodes : \A m \in Nodes \ {n} :
         /\ pc[n] \in {"wait", "cs"} => 
              /\ num[n] > 0
              /\ \/ /\ m \notin acks[n]
                    /\ \/ HasWriteOf(n,m,num[n])
                       \/ /\ ~ HasWriteOf(n,m,num[n])
                          /\ HasAck(m,n)
                          /\ rnum[m][n] = num[n]                              
                 \/ /\ m \in acks[n]
                    /\ rnum[m][n] = num[n]
Inv2 == \A n \in Nodes : \A m \in Nodes \ {n} :
         /\ /\ pc[n] = "wait" 
            /\ pc[m] \in {"wait", "cs"} 
            /\ m \in acks[n]
            => \/ rnum[n][m] = num[m]
               \/ <<num[n], n>> \ll <<num[m], m>>
 Inv3 == \A n \in Nodes : \A m \in Nodes \ {n} :
         /\ (pc[n] = "cs") /\ (pc[m] \in {"wait", "cs"})
               => <<num[n], n>> \ll <<num[m], m>>

(***************************************************************************)
(* The following rigamarole is to define reasonably precisely the set of   *)
(* possible values for net[m][n].                                          *)
(***************************************************************************)
(****
A ** B == {sa \o sb: sa \in A, sb \in B}
NZWrites == {<<Write(c)>> : c \in Nat \ {0}}

WriteSeqs == {<<>>, <<Write(0)>>} ** (NZWrites \cup {<< >>})

InsertAck(seq,i) == [j \in 1..(Len(seq)+1) |-> 
                      IF j < i THEN seq[j]
                                ELSE IF j = i THEN Ack
                                                ELSE seq[j-1]] 

InsertAcks(seq) == {InsertAck(seq,i) : i \in 1..(Len(seq)+1)}

MsgSeqs == WriteSeqs \cup UNION {InsertAcks(seq) : seq \in WriteSeqs }

ITypeOK == /\ /\ pc \in [Nodes \cup MsgThreads -> 
                  {"ncs", "enter", "wait", "cs", "exit", "a"}   ]
              /\ \A n \in Nodes : pc[n] # "a"
              /\ \A n \in MsgThreads : pc[n] = "a"
           /\ /\ num \in [Nodes -> Nat]
              /\ \A n \in Nodes : (num[n] = 0) <=> (pc[n] \in {"ncs", "enter"})
           /\ rnum \in {f \in [Nodes -> [Nodes -> Nat]] :
                             \A n \in Nodes : f[n][n] = 0}
           /\ acks \in [Nodes -> SUBSET Nodes]
           /\ \A n \in Nodes : 
                /\ n \notin acks[n]
                /\ (pc[n] \notin {"wait", "cs", "exit"}) => (acks[n] = { })
                /\ (pc[n] \in {"cs", "exit"}) => (acks[n] = Nodes \ {n})
           /\ /\ net \in [Nodes -> [Nodes -> MsgSeqs]] 
              /\ \A n \in Nodes : 
                    /\ net[n][n] = << >> 
                    /\ \A m \in Nodes \ {n} :
                         \A i \in 1..Len(net[n][m]) :
                            /\ (net[n][m][i].type = "write") => 
                                  (net[n][m][i].num \in {0, num[n]}) 
                            /\ (net[n][m][i].type = "ack") =>
                                  (pc[m] = "wait") /\ (m \notin acks[n])
           /\ /\ pc \in [Nodes \cup MsgThreads -> STRING]
              /\ \A n \in Nodes : pc[n] \in {"ncs", "enter", "wait", "cs", "exit"}
              /\ \A n \in MsgThreads : pc[n] = "a"

IInv == ITypeOK /\ Inv
********)
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
(***************************************************************************)
(* See DistBakery1a for an explanation of the following definitions.       *)
(***************************************************************************)
TestMaxNum == 4
TestNat == 0..(TestMaxNum + 1)

TestEdgeIds == {10*(-n) + (-m) : n, m \in Nodes} \ {10*(-n) + (-n) : n \in Nodes}
TestEdgeIdToEdge(eid) == <<-((eid) \div 10), -((eid) % 10)>> 
=============================================================================

-------------------------- MODULE ProtoBakeryTest --------------------------
EXTENDS Integers, FiniteSets

q \ll r == \/ q[1] < r[1]
           \/ /\ q[1] = r[1]
              /\ q[2] < r[2]

CONSTANT AnyNum
ASSUME AnyNum \notin Nat

CONSTANT Procs
ASSUME  /\ Procs \subseteq Int
        /\ IsFiniteSet(Procs)
(***************************************************************************)
(* Note: The algorithm is correct even if Procs contains 0 or 1 element.   *)
(* For 0 elements, the next-state action equals FALSE and the correctness  *)
(* conditions are vacuously true.  For 1 element, there are no             *)
(* subprocesses and the single process keeps looping forever, so           *)
(* starvation freedom is satisfied and mutual exclusion is trivially true. *)
(***************************************************************************)


SubProcs == {q \in Procs \X Procs : q[1] # q[2]}
subProcsOf(pid) == {q \in SubProcs : q[1] = pid[1]}
ProcIds == {<<p>> : p \in Procs}
Mirror(q) == <<q[2], q[1]>>
Wr0Procs == {<<q[1], q[2], "wr0">> : q \in SubProcs}
sprocOfW0(w) == <<w[1], w[2]>>

Min(S) == CHOOSE n \in S : \A m \in S \ {n} : m > n

(***************************************************************************)
(* The function with domain S that maps every element in S to v.           *)
(***************************************************************************)
ArrayOf(S,v) == [i \in S |-> v]

(***************************************************************************)
(* For pid in ProcIds and fcn an integer-valued function with domain       *)
(* SubProcs, this is the set of all positive integers m such that          *)
(*                                                                         *)
(*     <<fcn[q], q[2]>> \ll <<m, pid[1]>>                                  *)
(*                                                                         *)
(* for all q in subProcsOf(pid)                                            *)
(***************************************************************************)
GoodNums(pid, fcn) == { m \in Nat \ {0} : \A q \in subProcsOf(pid) :
                                            <<fcn[q], q[2]>> \ll <<m, pid[1]>> } 
(***************************************************************************)
(* For a function fcn with S a subset of its domain, this is the function  *)
(* obtained from fcn by executing  f[x] := val  for all x in S.            *)
(***************************************************************************)                                            
Replace(fcn, S, val) ==
  [x \in DOMAIN fcn |-> IF x \in S THEN val ELSE fcn[x]]                                            

(*********************
--algorithm ProtoBakery {

  variables num  = ArrayOf(Procs,0) ,
            temp = ArrayOf(SubProcs,0) ,
          mustRd = ArrayOf(SubProcs, TRUE) ;
 
  define {
    Before(p,q) == /\ pc[<<p>>] \in {"pcs", "cs"}
                   /\ \/ pc[<<q>>] \in {"ncs", "L1"}
                      \/ pc[<<q,p>>] = "M1s"
                      \/ /\ pc[<<q,p>>] = "L2" /\ pc[<<q>>] = "M1"
                         /\ temp[<<q,p>>] = num[p]
                      \/ /\ pc[<<q>>] \in {"pcs", "cs"}
                         /\ <<num[p],p>> \ll <<num[q],q>>
  }          

  fair process (subProc \in SubProcs) {
      M1s:  while (TRUE) {
              await pc[<<self[1]>>] = "M1" ;
              if (mustRd[self]) {
                temp[self] := num[self[2]] }
              else { with (v \in Nat) { temp[self] := v } } ;

      L2:    await /\ pc[<<self[1]>>] = "pcs" 
                   /\ Before(self[1],self[2]) \/ mustRd[<<self[1],self[2]>>] ;  
      L3:    await Before(self[1], self[2])  ;    
     scs:    await pc[<<self[1]>>] = "ncs"     }   }

  fair process (pid \in ProcIds) {                    
   ncs:- while (TRUE) {
              skip ;
              await \A q \in subProcsOf(self) : pc[q] = "M1s" ;
         L1:  mustRd := Replace(mustRd, {Mirror(p) : p \in subProcsOf(self)}, FALSE) ;
         
          M1: await \A q \in subProcsOf(self) : pc[q] = "L2" ;
              with (n \in {m \in Nat \ {0} : 
                      \A q \in subProcsOf(self) : 
                        \/ temp[q] = 0
                        \/ <<temp[q], q[1]>> \ll <<m, self[1]>>}) {
                 num[self[1]] := n } ;
              temp := Replace(temp, subProcsOf(self), 0) ;
              mustRd :=  Replace(mustRd, {Mirror(p) : p \in subProcsOf(self)}, TRUE) ;
              
         pcs: await \A q \in subProcsOf(self) : pc[q] = "scs" ;
         
          cs: skip ;
              num[self[1]] := 0 ;
              mustRd :=  Replace(mustRd, {Mirror(p) : p \in subProcsOf(self)}, FALSE)
              }   }
  
  fair process (wr \in Wr0Procs) {
    wr0: while (TRUE) {
           if (pc[<<self[1]>>] \in {"ncs", "L1"}) {
            mustRd[<<self[2], self[1]>>] := TRUE
             } }  } }
 *********************)
\* BEGIN TRANSLATION (chksum(pcal) = "63f29282" /\ chksum(tla) = "8800688a")
VARIABLES num, temp, mustRd, pc

(* define statement *)
Before(p,q) == /\ pc[<<p>>] \in {"pcs", "cs"}
               /\ \/ pc[<<q>>] \in {"ncs", "L1"}
                  \/ pc[<<q,p>>] = "M1s"
                  \/ /\ pc[<<q,p>>] = "L2" /\ pc[<<q>>] = "M1"
                     /\ temp[<<q,p>>] = num[p]
                  \/ /\ pc[<<q>>] \in {"pcs", "cs"}
                     /\ <<num[p],p>> \ll <<num[q],q>>


vars == << num, temp, mustRd, pc >>

ProcSet == (SubProcs) \cup (ProcIds) \cup (Wr0Procs)

Init == (* Global variables *)
        /\ num = ArrayOf(Procs,0)
        /\ temp = ArrayOf(SubProcs,0)
        /\ mustRd = ArrayOf(SubProcs, TRUE)
        /\ pc = [self \in ProcSet |-> CASE self \in SubProcs -> "M1s"
                                        [] self \in ProcIds -> "ncs"
                                        [] self \in Wr0Procs -> "wr0"]

M1s(self) == /\ pc[self] = "M1s"
             /\ pc[<<self[1]>>] = "M1"
             /\ IF mustRd[self]
                   THEN /\ temp' = [temp EXCEPT ![self] = num[self[2]]]
                   ELSE /\ \E v \in Nat:
                             temp' = [temp EXCEPT ![self] = v]
             /\ pc' = [pc EXCEPT ![self] = "L2"]
             /\ UNCHANGED << num, mustRd >>

L2(self) == /\ pc[self] = "L2"
            /\ /\ pc[<<self[1]>>] = "pcs"
               /\ Before(self[1],self[2]) \/ mustRd[<<self[1],self[2]>>]
            /\ pc' = [pc EXCEPT ![self] = "L3"]
            /\ UNCHANGED << num, temp, mustRd >>

L3(self) == /\ pc[self] = "L3"
            /\ Before(self[1], self[2])
            /\ pc' = [pc EXCEPT ![self] = "scs"]
            /\ UNCHANGED << num, temp, mustRd >>

scs(self) == /\ pc[self] = "scs"
             /\ pc[<<self[1]>>] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "M1s"]
             /\ UNCHANGED << num, temp, mustRd >>

subProc(self) == M1s(self) \/ L2(self) \/ L3(self) \/ scs(self)

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ \A q \in subProcsOf(self) : pc[q] = "M1s"
             /\ pc' = [pc EXCEPT ![self] = "L1"]
             /\ UNCHANGED << num, temp, mustRd >>

L1(self) == /\ pc[self] = "L1"
            /\ mustRd' = Replace(mustRd, {Mirror(p) : p \in subProcsOf(self)}, FALSE)
            /\ pc' = [pc EXCEPT ![self] = "M1"]
            /\ UNCHANGED << num, temp >>

M1(self) == /\ pc[self] = "M1"
            /\ \A q \in subProcsOf(self) : pc[q] = "L2"
            /\ \E n \in     {m \in Nat \ {0} :
                        \A q \in subProcsOf(self) :
                          \/ temp[q] = 0
                          \/ <<temp[q], q[1]>> \ll <<m, self[1]>>}:
                 num' = [num EXCEPT ![self[1]] = n]
            /\ temp' = Replace(temp, subProcsOf(self), 0)
            /\ mustRd' = Replace(mustRd, {Mirror(p) : p \in subProcsOf(self)}, TRUE)
            /\ pc' = [pc EXCEPT ![self] = "pcs"]

pcs(self) == /\ pc[self] = "pcs"
             /\ \A q \in subProcsOf(self) : pc[q] = "scs"
             /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << num, temp, mustRd >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ num' = [num EXCEPT ![self[1]] = 0]
            /\ mustRd' = Replace(mustRd, {Mirror(p) : p \in subProcsOf(self)}, FALSE)
            /\ pc' = [pc EXCEPT ![self] = "ncs"]
            /\ temp' = temp

pid(self) == ncs(self) \/ L1(self) \/ M1(self) \/ pcs(self) \/ cs(self)

wr0(self) == /\ pc[self] = "wr0"
             /\ IF pc[<<self[1]>>] \in {"ncs", "L1"}
                   THEN /\ mustRd' = [mustRd EXCEPT ![<<self[2], self[1]>>] = TRUE]
                   ELSE /\ TRUE
                        /\ UNCHANGED mustRd
             /\ pc' = [pc EXCEPT ![self] = "wr0"]
             /\ UNCHANGED << num, temp >>

wr(self) == wr0(self)

Next == (\E self \in SubProcs: subProc(self))
           \/ (\E self \in ProcIds: pid(self))
           \/ (\E self \in Wr0Procs: wr(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in SubProcs : WF_vars(subProc(self))
        /\ \A self \in ProcIds : WF_vars((pc[self] # "ncs") /\ pid(self))
        /\ \A self \in Wr0Procs : WF_vars(wr(self))

\* END TRANSLATION 
-----------------------------------------------------------------------------

TypeOK == /\ num  \in [Procs -> Nat]
          /\ mustRd \in [SubProcs -> BOOLEAN]
          /\ temp \in [SubProcs -> Nat]  
          /\ pc \in [ProcSet -> STRING]

\*InNCS(p) == \A q \in subProcsOf(p) : pc[q] = "enter"
InCS(p)  == (pc[p] = "cs") 
\*InCS(p)  == (pc[p] = "cs")

Mutex == \A p \in ProcIds : \A q \in ProcIds \ {p} : ~(InCS(p) /\ InCS(q))

StarvationFree == \A p \in ProcIds : (pc[p] = "L1") ~> InCS(p) 
-----------------------------------------------------------------------------
TestMaxNum == 8
TestNat == 0..(TestMaxNum + 1)
(***************************************************************************
2 Procs, TestMaxNum = 4: 698 states in :05 on laptop 
2 Procs, TestMaxNum = 6: 1114 states in :11 on laptop   
2 Procs, TestMaxNum = 8: 1618 states in :10 on laptop 
3 Procs, TestMaxNum = 6: 1,501,668 states in 10:13 + 1:23 on Azure
4 Procs, TestMaxNum = 3: canceled after 48,970,253 states in 12:15:03 when
                          queue size graph indicated it was less than 1/5 done.

 ***************************************************************************)

=============================================================================
\* Modification History
\* Last modified Sun Mar 28 06:51:07 PDT 2021 by lamport
\* Created Mon Mar 08 17:10:33 PST 2021 by lamport

