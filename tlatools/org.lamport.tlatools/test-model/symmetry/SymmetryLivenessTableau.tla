---------------------- MODULE SymmetryLivenessTableau ----------------------
VARIABLES mem, ctl, buf
VARIABLE memInt
CONSTANTS  Proc,  
           Adr,  
           Val

NoVal == CHOOSE x : x \notin Val 
InitMemInt == {<<p, NoVal>> : p \in Proc}
Send(p, d, oldMemInt, newMemInt)  ==  newMemInt = <<p, d>>
Reply(p, d, oldMemInt, newMemInt) ==  newMemInt = <<p, d>>
(***************************************************************************)
(* We comment out the assumption because TLC cannot handle unbounded       *)
(* quantifiers.                                                            *)
(***************************************************************************)
\* ASSUME \A p, d, miOld, miNew : 
\*         /\ Send(p,d,miOld,miNew)  \in BOOLEAN
\*         /\ Reply(p,d,miOld,miNew) \in BOOLEAN  

-----------------------------------------------------------------------------
MReq == [op : {"Rd"}, adr: Adr] 
          \cup [op : {"Wr"}, adr: Adr, val : Val]

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

Spec == IInit  /\  [][INext]_<<memInt, mem, ctl, buf>>
             /\ \A p \in Proc : WF_<<memInt, mem, ctl, buf>>(Do(p) \/ Rsp(p))
 
Liveness == \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")
--------------------------------------------------------------
THEOREM Spec => []TypeInvariant
==============================================================