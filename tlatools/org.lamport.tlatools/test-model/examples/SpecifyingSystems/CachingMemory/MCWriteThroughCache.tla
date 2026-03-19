------------------------- MODULE MCWriteThroughCache ------------------------
(***************************************************************************)
(* This is a module used for running TLC to check the specification of the *)
(* write-through cache in module WriteThroughCache.  Because TLC version 1 *)
(* can't handle instantiation, we use module WriteThroughCacheInstanced in *)
(* its stead.  We check that the specification satisfies the type          *)
(* invariant and the invariant Coherence.  We also check that it           *)
(* implements the InternalMemory specification under the refinement        *)
(* mapping described in the section "Proving Implementation".              *)
(***************************************************************************)

EXTENDS WriteThroughCacheInstanced

(***************************************************************************)
(* The following definitions are substituted for the constants Send,       *)
(* Reply, and InitMemInt of the MemoryFace module.  See                    *)
(* MCInternalMemory.tla for their explanations.                            *)
(***************************************************************************)
MCSend(p, d, oldMemInt, newMemInt)  ==  newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) ==  newMemInt = <<p, d>>
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

(***************************************************************************)
(* As described in the section titled "Proving Implementation", the        *)
(* write-through cache specifies Spec satisfies                            *)
(*                                                                         *)
(*    Spec => LM!Inner(omem, octl, obuf)!ISpec                             *)
(*                                                                         *)
(* for the following choices of omem, octl, and obuf:                      *)
(***************************************************************************)

   omem == vmem
   octl == [p \in Proc |-> IF ctl[p] = "waiting" THEN "busy" ELSE ctl[p]]
   obuf == buf

(***************************************************************************)
(* Formula LM!Inner(omem, octl, obuf)!ISpec consists of formula ISpec of   *)
(* module InternalMemory with the substitutions                            *)
(*                                                                         *)
(* (+)   mem <- omem, ctl <- octl, buf <- obuf                             *)
(*                                                                         *)
(* Because TLC Version 1 cannot handle instantiation, we now do the        *)
(* instantiation "by hand".  So, below is a copy of module InternalMemory  *)
(* with the substitutions (+) made, and with the names of all defined      *)
(* operators prefixed with "LM_Inner_".  (Had we used the actual INSTANCE  *)
(* statements, those names would actually be prefixed by                   *)
(* "LM!Inner(mem, ctl, buf)!", where mem, ctl, and buf would be parameters *)
(* of the definitions.)                                                    *)
(***************************************************************************)

LM_Inner_IInit == /\ omem \in [Adr->Val]
                  /\ octl = [p \in Proc |-> "rdy"] 
                  /\ obuf = [p \in Proc |-> NoVal] 
                  /\ memInt \in InitMemInt

LM_Inner_TypeInvariant == 
  /\ omem \in [Adr->Val]
  /\ octl \in [Proc -> {"rdy", "busy","done"}] 
  /\ obuf \in [Proc -> MReq \cup Val \cup {NoVal}]

LM_Inner_Req(p) == /\ octl[p] = "rdy" 
          /\ \E req \in  MReq : 
                /\ Send(p, req, memInt, memInt') 
                /\ obuf' = [obuf EXCEPT ![p] = req]
                /\ octl' = [octl EXCEPT ![p] = "busy"]
          /\ UNCHANGED omem 

LM_Inner_Do(p) == 
  /\ octl[p] = "busy" 
  /\ omem' = IF obuf[p].op = "Wr"
              THEN [omem EXCEPT ![obuf[p].adr] = obuf[p].val] 
              ELSE omem 
  /\ obuf' = [obuf EXCEPT ![p] = IF obuf[p].op = "Wr"
                                  THEN NoVal
                                  ELSE omem[obuf[p].adr]]
  /\ octl' = [octl EXCEPT ![p] = "done"] 
  /\ UNCHANGED memInt 

LM_Inner_Rsp(p) == /\ octl[p] = "done"
                   /\ Reply(p, obuf[p], memInt, memInt')
                   /\ octl' = [octl EXCEPT ![p]= "rdy"]
                   /\ UNCHANGED <<omem, obuf>> 

LM_Inner_INext == 
     \E p \in Proc: LM_Inner_Req(p) \/ LM_Inner_Do(p) \/ LM_Inner_Rsp(p) 

LM_Inner_ISpec == 
    LM_Inner_IInit  /\  [][LM_Inner_INext]_<<memInt, omem, octl, obuf>>
-----------------------------------------------------------------------------
THEOREM LM_Inner_ISpec => []LM_Inner_TypeInvariant
=============================================================================