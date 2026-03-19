-------------------------- MODULE MemoryInterface ---------------------------
VARIABLE memInt
CONSTANTS  Send(_, _, _, _),
           Reply(_, _, _, _),
           InitMemInt, 
           Proc,  
           Adr,  
           Val

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

NoVal == CHOOSE v : v \notin Val
=============================================================================
