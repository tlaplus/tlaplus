------------------------ MODULE InnerSequential -----------------------------
EXTENDS RegisterInterface, Naturals, Sequences, FiniteSets
VARIABLE opQ, mem
-----------------------------------------------------------------------------
Done    == CHOOSE v : v \notin Reg
-----------------------------------------------------------------------------
DataInvariant == 
  /\ RegFileTypeInvariant
  /\ opQ \in [Proc -> Seq([req : Request, reg : Reg \cup {Done}])]
  /\ mem \in [Adr -> Val]
  /\ \A p \in Proc : \A r \in Reg :
       Cardinality ({i \in DOMAIN opQ[p] : opQ[p][i].reg = r})
         = IF regFile[p][r].op = "Free" THEN 0 ELSE 1

Init == /\ regFile \in [Proc -> [Reg -> FreeRegValue]]
        /\ opQ = [p \in Proc |-> << >>]
        /\ mem \in [Adr -> Val]
-----------------------------------------------------------------------------
IssueRequest(proc, req, reg) ==
  /\ regFile[proc][reg].op = "Free"
  /\ regFile' = [regFile EXCEPT ![proc][reg] = req]
  /\ opQ' = [opQ EXCEPT ![proc] = Append(@, [req |-> req, reg |-> reg])]
  /\ UNCHANGED mem

RespondToRd(proc, reg) ==
  /\ regFile[proc][reg].op = "Rd"
  /\ \E val \in Val : 
       /\ regFile' = [regFile EXCEPT ![proc][reg].val = val,
                                     ![proc][reg].op  = "Free"]
       /\ opQ' = LET idx == CHOOSE i \in DOMAIN opQ[proc] : 
                                         opQ[proc][i].reg = reg
                 IN [opQ EXCEPT ![proc][idx].req.val = val,
                                ![proc][idx].reg     = Done ]
  /\ UNCHANGED mem

RespondToWr(proc, reg) ==
  /\ regFile[proc][reg].op = "Wr"
  /\ regFile' = [regFile EXCEPT ![proc][reg].op  = "Free"]
  /\ LET idx == CHOOSE i \in DOMAIN opQ[proc] : opQ[proc][i].reg = reg
     IN  opQ' = [opQ EXCEPT ![proc][idx].reg = Done]
  /\ UNCHANGED mem

RemoveOp(proc) ==
  /\ opQ[proc] # << >>
  /\ Head(opQ[proc]).reg = Done  
  /\ mem' = IF Head(opQ[proc]).req.op = "Rd"
              THEN mem
              ELSE [mem EXCEPT ![Head(opQ[proc]).req.adr] = 
                                   Head(opQ[proc]).req.val]
  /\ opQ' = [opQ EXCEPT ![proc] = Tail(@)]
  /\ UNCHANGED regFile

Internal(proc)  == 
    /\ RemoveOp(proc)
    /\ (Head(opQ[proc]).req.op = "Rd") =>
            (mem[Head(opQ[proc]).req.adr] = Head(opQ[proc]).req.val)

Next == \E proc \in Proc:
           \/ \E reg \in Reg :
                  \/ \E req \in Request : IssueRequest(proc, req, reg)
                  \/ RespondToRd(proc, reg)
                  \/ RespondToWr(proc, reg)
           \/ Internal(proc)
-----------------------------------------------------------------------------
Spec ==
  /\ Init 
  /\ [][Next]_<<regFile, opQ, mem>>
  /\ \A proc \in Proc, reg \in Reg :
        WF_<<regFile, opQ, mem>>(RespondToRd(proc, reg) 
                                        \/ RespondToWr(proc, reg))
  /\ \A proc \in Proc : WF_<<regFile, opQ, mem>>(RemoveOp(proc))

-----------------------------------------------------------------------------
THEOREM Spec => []DataInvariant
=============================================================================
