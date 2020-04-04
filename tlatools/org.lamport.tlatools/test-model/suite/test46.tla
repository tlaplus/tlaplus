--------------------- MODULE test46 -----------------------

(* This found a bug in Version 1.03 of 18 Oct 1999 *)

EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANT Reg, Adr, Val, Proc
VARIABLE reqQ, reqOrder

Request    == [adr : Adr, val : Val, op : {"Rd", "Wr"}]
FreeRegVal == [adr : Adr, val : Val, op : {"Free"}]

reqId == UNION { [proc : {p}, idx : DOMAIN reqQ[p]] : p \in Proc }

oi \prec oj == <<oi, oj>> \in reqOrder

TypeInvariant == 
  /\ reqQ \in [Proc -> Seq(Request \cup [reg : Reg])]
  /\ reqOrder \in SUBSET (reqId \X reqId)

Init == /\ reqQ = [p \in Proc |-> << >>]
        /\ reqOrder = {}

GoodReqOrder ==
  /\ \A oi, oj, ok \in reqId : (oi \prec oj) /\ (oj \prec ok) => (oi \prec ok)
  /\ \A oi \in reqId : ~(oi \prec oi)
  /\ \A oi, oj \in reqId : 
        (oi.proc = oj.proc) /\ (oi.idx < oj.idx) => (oi \prec oj)

-----------------------------------------------------------------------------
UpdateReqOrder == 
  /\ reqOrder' \in SUBSET(reqId' \X reqId')
  /\ reqOrder \subseteq reqOrder'
  /\ GoodReqOrder'

IssueRequest(proc, req, reg) ==
  (*************************************************************************)
  (* The action by which processor proc issues request req in register     *)
  (* reg.                                                                  *)
  (*************************************************************************)
  /\ reqQ' = [reqQ EXCEPT ![proc] = Append(@, [reg |-> reg])]
  /\ UpdateReqOrder


Next == \E proc \in Proc, reg \in Reg :
           \E req \in Request : IssueRequest(proc, req, reg)


Constraint == \A p \in Proc : Len(reqQ[p]) < 2
=============================================================================
