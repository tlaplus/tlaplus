------------------ MODULE InternalMemory ---------------------
EXTENDS MemoryInterface
VARIABLES mem, ctl, buf
--------------------------------------------------------------
IInit == /\ mem \in [Adr->Val]
         /\ ctl = [p \in Proc |-> "rdy"] 
         /\ buf = [p \in Proc |-> NoVal] 
         /\ memInt \in InitMemInt

TypeInvariant == 
  /\ mem \in [Adr->Val]
  /\ ctl \in [Proc -> {"rdy", "busy","done"}] 
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]

Req(p) == /\ ctl[p] = "rdy" 
          /\ \E req \in  MReq : 
                /\ Send(p, req, memInt, memInt') 
                /\ buf' = [buf EXCEPT ![p] = req]
                /\ ctl' = [ctl EXCEPT ![p] = "busy"]
          /\ UNCHANGED mem 

Do(p) == 
  /\ ctl[p] = "busy" 
  /\ mem' = IF buf[p].op = "Wr"
              THEN [mem EXCEPT ![buf[p].adr] = buf[p].val] 
              ELSE mem 
  /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr"
                                  THEN NoVal
                                  ELSE mem[buf[p].adr]]
  /\ ctl' = [ctl EXCEPT ![p] = "done"] 
  /\ UNCHANGED memInt 

Rsp(p) == /\ ctl[p] = "done"
          /\ Reply(p, buf[p], memInt, memInt')
          /\ ctl' = [ctl EXCEPT ![p]= "rdy"]
          /\ UNCHANGED <<mem, buf>> 

INext == \E p \in Proc: Req(p) \/ Do(p) \/ Rsp(p) 

ISpec == IInit  /\  [][INext]_<<memInt, mem, ctl, buf>>
--------------------------------------------------------------
THEOREM ISpec => []TypeInvariant
==============================================================
