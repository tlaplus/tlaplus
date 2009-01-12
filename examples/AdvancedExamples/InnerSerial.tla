-------------------------- MODULE InnerSerial -------------------------------
EXTENDS RegisterInterface, Naturals, Sequences, FiniteSets, TLC
CONSTANT InitMem
VARIABLE opQ, opOrder
-----------------------------------------------------------------------------
opId      == UNION { [proc : {p}, idx : DOMAIN opQ[p]] : p \in Proc }
opIdQ(oi) == opQ[oi.proc][oi.idx]

InitWr  == CHOOSE v : v \notin [proc : Proc, idx : Nat]

Done == CHOOSE v : v \notin Reg

opVal ==      [req : Request,   reg : Reg]         
         \cup [req : WrRequest, reg : {Done}]  
         \cup [req : RdRequest, reg : {Done}, source : opId \cup {InitWr}]

goodSource(oi) == 
  {InitWr} \cup {o \in opId : /\ opIdQ(o).req.op  = "Wr"
                              /\ opIdQ(o).req.adr = opIdQ(oi).req.adr}
-----------------------------------------------------------------------------
DataInvariant == 
  /\ RegFileTypeInvariant

  /\ opQ \in [Proc -> Seq(opVal)]

  /\ opOrder \subseteq (opId \X opId)

  /\ \A oi \in opId :
       /\ ("source" \in DOMAIN opIdQ(oi)) => 
             /\ opIdQ(oi).source \in goodSource(oi)
             /\ opIdQ(oi).req.val = 
                   IF opIdQ(oi).source = InitWr
                     THEN InitMem[opIdQ(oi).req.adr]
                     ELSE opIdQ(opIdQ(oi).source).req.val
       /\ (opIdQ(oi).reg # Done) => 
             (opIdQ(oi).req = regFile[oi.proc][opIdQ(oi).reg])

  /\ \A p \in Proc : \A r \in Reg :
       Cardinality ({i \in DOMAIN opQ[p] : opQ[p][i].reg = r})
         = IF regFile[p][r].op = "Free" THEN 0 ELSE 1

Init == /\ regFile \in [Proc -> [Reg -> FreeRegValue]]
        /\ opQ = [p \in Proc |-> << >>]
        /\ opOrder = {}

totalOpOrder  ==
  {R \in SUBSET (opId \X opId) :
     /\ \A oi, oj \in opId : 
             (oi = oj) \/ (<<oi, oj>> \in R)  \/ (<<oj, oi>> \in R)
     /\ \A oi, oj, ok \in opId : 
           (<<oi, oj>> \in R)  /\ (<<oj, ok>> \in R) => (<<oi, ok>> \in R)
     /\ \A oi \in opId : <<oi, oi>> \notin R }

Serializable ==
  \E R \in totalOpOrder :
     /\ opOrder \subseteq R
     /\ \A oi, oj \in opId :
          (oi.proc = oj.proc) /\ (oi.idx < oj.idx) => (<<oi, oj>> \in R)
     /\ \A oi \in opId : 
           ("source" \in DOMAIN opIdQ(oi)) =>
               ~ ( \E oj \in goodSource(oi) : 
                      /\ <<oj, oi>> \in R
                      /\ (opIdQ(oi).source # InitWr) => 
                            (<<opIdQ(oi).source, oj>> \in R) )
-----------------------------------------------------------------------------
UpdateOpOrder == 
  /\ opOrder' \in SUBSET(opId' \X opId')
  /\ opOrder \subseteq opOrder'
  /\ Serializable'

IssueRequest(proc, req, reg) ==
  /\ regFile[proc][reg].op = "Free"
  /\ regFile' = [regFile EXCEPT ![proc][reg] = req]
  /\ opQ' = [opQ EXCEPT ![proc] = Append(@, [req |-> req, reg |-> reg])]
  /\ UpdateOpOrder

RespondToWr(proc, reg) ==
  /\ regFile[proc][reg].op = "Wr"
  /\ regFile' = [regFile EXCEPT ![proc][reg].op  = "Free"]
  /\ LET idx == CHOOSE i \in DOMAIN opQ[proc] : opQ[proc][i].reg = reg
     IN  opQ' = [opQ EXCEPT ![proc][idx].reg = Done]
  /\ UpdateOpOrder

RespondToRd(proc, reg) ==
  LET req == regFile[proc][reg]
      idx == CHOOSE i \in DOMAIN opQ[proc] : opQ[proc][i].reg = reg
  IN  /\ req.op = "Rd"
      /\ \E src \in goodSource([proc |-> proc, idx |-> idx]) :
           LET val == IF src = InitWr THEN InitMem[req.adr]
                                      ELSE opIdQ(src).req.val
           IN  /\ regFile' = [regFile EXCEPT ![proc][reg].val = val,
                                             ![proc][reg].op  = "Free"]
               /\ opQ' = [opQ EXCEPT ![proc][idx] = 
                            [req    |-> [req EXCEPT !.val = val],
                             reg    |-> Done,
                             source |-> src  ]]
      /\ UpdateOpOrder

Internal ==
   /\ UNCHANGED <<regFile, opQ>>
   /\ UpdateOpOrder

Next == \/ \E proc \in Proc, reg \in Reg :
             \/ \E req \in Request : IssueRequest(proc, req, reg)
             \/ RespondToRd(proc, reg)
             \/ RespondToWr(proc, reg)
        \/ Internal
-----------------------------------------------------------------------------
Spec ==
  /\ Init 
  /\ [][Next]_<<regFile, opQ, opOrder>>
  /\ \A proc \in Proc, reg \in Reg :
      WF_<<regFile, opQ, opOrder>>(RespondToWr(proc, reg) 
                                        \/ RespondToRd(proc, reg) )
  /\ \A oi, oj \in [proc : Proc, idx : Nat] : 
       (oi # oj) => 
             WF_<<regFile, opQ, opOrder>>(
                   /\ (oi \in opId) /\ (oj \in opId)
                   /\ Internal
                   /\ (<<oi, oj>> \in opOrder') \/ (<<oj, oi>> \in opOrder'))

=============================================================================
