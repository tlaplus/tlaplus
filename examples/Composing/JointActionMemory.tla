------------------------ MODULE JointActionMemory ---------------------------
EXTENDS MemoryInterface

   -------------------- MODULE InnerEnvironmentComponent --------------------
   VARIABLE rdy
   IE  == rdy = [p \in Proc |-> TRUE] 

   Erqst(p) == /\ rdy[p]
               /\ \E req \in MReq : Send(p, req,  memInt, memInt') 
               /\ rdy' = [rdy EXCEPT ![p] = FALSE]

   ERsp(p)  == /\ \E rsp \in Val \cup {NoVal} : 
                       Reply(p, rsp,  memInt, memInt') 
               /\ rdy' = [rdy EXCEPT ![p] = TRUE]

   NE == \E p \in Proc : Erqst(p) \/ ERsp(p)

   IESpec == IE /\ [][NE]_<<memInt, rdy>>
   ==========================================================================

   ---------------------- MODULE InnerMemoryComponent -----------------------
   EXTENDS InternalMemory
   MRqst(p) ==   /\ \E req \in MReq : 
                      /\ Send(p, req, memInt, memInt') 
                      /\ buf' = [buf EXCEPT ![p] = req]
                      /\ ctl' = [ctl EXCEPT ![p] = "busy"]
                 /\ UNCHANGED mem 

   NM == \E p \in Proc : MRqst(p) \/ Do(p) \/ Rsp(p)

   IMSpec == IInit /\ [][NM]_<<memInt, mem, ctl, buf>>
   ==========================================================================

IEnv(rdy) == INSTANCE InnerEnvironmentComponent

IMem(mem, ctl, buf) == INSTANCE InnerMemoryComponent

Spec == /\ \EE rdy : IEnv(rdy)!IESpec  
        /\ \EE mem, ctl, buf : IMem(mem,ctl,buf)!IMSpec
=============================================================================
